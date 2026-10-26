import V185TrunkScan22Chunk100

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_906758 : List Nat := [6, 2, 1, 1, 2, 2, 1, 1, 1, 5]
def baseStart_906758 : Nat := 118140960795 + 906758 * 2 ^ 59
def prefixEnd_906758 : Nat := 4983230072969 + 3 ^ 40 * 906758 * 2
def baseEnd_906758 : Nat := 310401794206445692569935

theorem tailTrace_906758 : CollatzResearch.WordTrace tailWord_906758 prefixEnd_906758 310401794206445692569935 := by
  unfold tailWord_906758
  simp only [CollatzResearch.WordTrace]
  refine ⟨1033505664030565711947529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22048120832652068521547285 1033505664030565711947529)
  ·
    refine ⟨775129248022924283960647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1033505664030565711947529 775129248022924283960647)
    ·
      refine ⟨1162693872034386425940971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 775129248022924283960647 1162693872034386425940971)
      ·
        refine ⟨1744040808051579638911457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1162693872034386425940971 1744040808051579638911457)
        ·
          refine ⟨1308030606038684729183593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1744040808051579638911457 1308030606038684729183593)
          ·
            refine ⟨981022954529013546887695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1308030606038684729183593 981022954529013546887695)
            ·
              refine ⟨1471534431793520320331543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 981022954529013546887695 1471534431793520320331543)
              ·
                refine ⟨2207301647690280480497315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1471534431793520320331543 2207301647690280480497315)
                ·
                  refine ⟨3310952471535420720745973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2207301647690280480497315 3310952471535420720745973)
                  ·
                    refine ⟨310401794206445692569935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3310952471535420720745973 310401794206445692569935)
                    ·
                      rfl

theorem cell22_906758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_906758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_906758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_906758 prefixEnd_906758 := by exact prefixLift 906758
  have htrace : WordTrace (prefixWord ++ tailWord_906758) baseStart_906758 baseEnd_906758 := by
    simpa [prefixWord, tailWord_906758, baseEnd_906758] using wordTrace_append hprefix tailTrace_906758
  have hstable : (prefixWord ++ tailWord_906758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906758).length < 2 ^ (prefixWord ++ tailWord_906758).sum := by decide
  have hdescent : baseEnd_906758 < baseStart_906758 := by decide
  rcases family_descends (prefixWord ++ tailWord_906758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906829 : List Nat := [1, 6, 1, 1, 3, 1, 1, 1, 3, 4]
def baseStart_906829 : Nat := 118140960795 + 906829 * 2 ^ 59
def prefixEnd_906829 : Nat := 4983230072969 + 3 ^ 40 * 906829 * 2
def baseEnd_906829 : Nat := 310426098957425174044717

theorem tailTrace_906829 : CollatzResearch.WordTrace tailWord_906829 prefixEnd_906829 310426098957425174044717 := by
  unfold tailWord_906829
  simp only [CollatzResearch.WordTrace]
  refine ⟨33074770831720881908155541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22049847221147254605437027 33074770831720881908155541)
  ·
    refine ⟨1550379882736916339444791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 33074770831720881908155541 1550379882736916339444791)
    ·
      refine ⟨2325569824105374509167187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1550379882736916339444791 2325569824105374509167187)
      ·
        refine ⟨3488354736158061763750781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2325569824105374509167187 3488354736158061763750781)
        ·
          refine ⟨1308133026059273161406543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3488354736158061763750781 1308133026059273161406543)
          ·
            refine ⟨1962199539088909742109815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1308133026059273161406543 1962199539088909742109815)
            ·
              refine ⟨2943299308633364613164723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1962199539088909742109815 2943299308633364613164723)
              ·
                refine ⟨4414948962950046919747085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2943299308633364613164723 4414948962950046919747085)
                ·
                  refine ⟨1655605861106267594905157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4414948962950046919747085 1655605861106267594905157)
                  ·
                    refine ⟨310426098957425174044717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1655605861106267594905157 310426098957425174044717)
                    ·
                      rfl

theorem cell22_906829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_906829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_906829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_906829 prefixEnd_906829 := by exact prefixLift 906829
  have htrace : WordTrace (prefixWord ++ tailWord_906829) baseStart_906829 baseEnd_906829 := by
    simpa [prefixWord, tailWord_906829, baseEnd_906829] using wordTrace_append hprefix tailTrace_906829
  have hstable : (prefixWord ++ tailWord_906829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906829).length < 2 ^ (prefixWord ++ tailWord_906829).sum := by decide
  have hdescent : baseEnd_906829 < baseStart_906829 := by decide
  rcases family_descends (prefixWord ++ tailWord_906829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906885 : List Nat := [1, 3, 1, 1, 4, 1, 1, 2, 2, 6]
def baseStart_906885 : Nat := 118140960795 + 906885 * 2 ^ 59
def prefixEnd_906885 : Nat := 4983230072969 + 3 ^ 40 * 906885 * 2
def baseEnd_906885 : Nat := 310445268901859694644545

theorem tailTrace_906885 : CollatzResearch.WordTrace tailWord_906885 prefixEnd_906885 310445268901859694644545 := by
  unfold tailWord_906885
  simp only [CollatzResearch.WordTrace]
  refine ⟨33076813319518003472194109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22051208879678668981462739 33076813319518003472194109)
  ·
    refine ⟨12403804994819251302072791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33076813319518003472194109 12403804994819251302072791)
    ·
      refine ⟨18605707492228876953109187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12403804994819251302072791 18605707492228876953109187)
      ·
        refine ⟨27908561238343315429663781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18605707492228876953109187 27908561238343315429663781)
        ·
          refine ⟨5232855232189371643061959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27908561238343315429663781 5232855232189371643061959)
          ·
            refine ⟨7849282848284057464592939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5232855232189371643061959 7849282848284057464592939)
            ·
              refine ⟨11773924272426086196889409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7849282848284057464592939 11773924272426086196889409)
              ·
                refine ⟨8830443204319564647667057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11773924272426086196889409 8830443204319564647667057)
                ·
                  refine ⟨6622832403239673485750293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8830443204319564647667057 6622832403239673485750293)
                  ·
                    refine ⟨310445268901859694644545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6622832403239673485750293 310445268901859694644545)
                    ·
                      rfl

theorem cell22_906885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 6].length) (baseStart_906885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_906885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_906885 prefixEnd_906885 := by exact prefixLift 906885
  have htrace : WordTrace (prefixWord ++ tailWord_906885) baseStart_906885 baseEnd_906885 := by
    simpa [prefixWord, tailWord_906885, baseEnd_906885] using wordTrace_append hprefix tailTrace_906885
  have hstable : (prefixWord ++ tailWord_906885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906885).length < 2 ^ (prefixWord ++ tailWord_906885).sum := by decide
  have hdescent : baseEnd_906885 < baseStart_906885 := by decide
  rcases family_descends (prefixWord ++ tailWord_906885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906887 : List Nat := [1, 1, 4, 2, 1, 3, 1, 1, 5, 3]
def baseStart_906887 : Nat := 118140960795 + 906887 * 2 ^ 59
def prefixEnd_906887 : Nat := 4983230072969 + 3 ^ 40 * 906887 * 2
def baseEnd_906887 : Nat := 310445953542732356094539

theorem tailTrace_906887 : CollatzResearch.WordTrace tailWord_906887 prefixEnd_906887 310445953542732356094539 := by
  unfold tailWord_906887
  simp only [CollatzResearch.WordTrace]
  refine ⟨33076886265510757813766915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22051257510340505209177943 33076886265510757813766915)
  ·
    refine ⟨49615329398266136720650373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33076886265510757813766915 49615329398266136720650373)
    ·
      refine ⟨9302874262174900635121945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49615329398266136720650373 9302874262174900635121945)
      ·
        refine ⟨6977155696631175476341459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9302874262174900635121945 6977155696631175476341459)
        ·
          refine ⟨10465733544946763214512189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6977155696631175476341459 10465733544946763214512189)
          ·
            refine ⟨3924650079355036205442071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10465733544946763214512189 3924650079355036205442071)
            ·
              refine ⟨5886975119032554308163107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3924650079355036205442071 5886975119032554308163107)
              ·
                refine ⟨8830462678548831462244661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5886975119032554308163107 8830462678548831462244661)
                ·
                  refine ⟨827855876113952949585437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8830462678548831462244661 827855876113952949585437)
                  ·
                    refine ⟨310445953542732356094539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 827855876113952949585437 310445953542732356094539)
                    ·
                      rfl

theorem cell22_906887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 5, 3].length) (baseStart_906887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_906887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_906887 prefixEnd_906887 := by exact prefixLift 906887
  have htrace : WordTrace (prefixWord ++ tailWord_906887) baseStart_906887 baseEnd_906887 := by
    simpa [prefixWord, tailWord_906887, baseEnd_906887] using wordTrace_append hprefix tailTrace_906887
  have hstable : (prefixWord ++ tailWord_906887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906887).length < 2 ^ (prefixWord ++ tailWord_906887).sum := by decide
  have hdescent : baseEnd_906887 < baseStart_906887 := by decide
  rcases family_descends (prefixWord ++ tailWord_906887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906915 : List Nat := [1, 1, 1, 4, 1, 1, 3, 1, 4, 5]
def baseStart_906915 : Nat := 118140960795 + 906915 * 2 ^ 59
def prefixEnd_906915 : Nat := 4983230072969 + 3 ^ 40 * 906915 * 2
def baseEnd_906915 : Nat := 310455538514949616394453

theorem tailTrace_906915 : CollatzResearch.WordTrace tailWord_906915 prefixEnd_906915 310455538514949616394453 := by
  unfold tailWord_906915
  simp only [CollatzResearch.WordTrace]
  refine ⟨33077907509409318595786199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22051938339606212397190799 33077907509409318595786199)
  ·
    refine ⟨49616861264113977893679299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33077907509409318595786199 49616861264113977893679299)
    ·
      refine ⟨74425291896170966840518949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49616861264113977893679299 74425291896170966840518949)
      ·
        refine ⟨13954742230532056282597303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74425291896170966840518949 13954742230532056282597303)
        ·
          refine ⟨20932113345798084423895955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13954742230532056282597303 20932113345798084423895955)
          ·
            refine ⟨31398170018697126635843933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20932113345798084423895955 31398170018697126635843933)
            ·
              refine ⟨11774313757011422488441475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31398170018697126635843933 11774313757011422488441475)
              ·
                refine ⟨17661470635517133732662213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11774313757011422488441475 17661470635517133732662213)
                ·
                  refine ⟨3311525744159462574874165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17661470635517133732662213 3311525744159462574874165)
                  ·
                    refine ⟨310455538514949616394453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3311525744159462574874165 310455538514949616394453)
                    ·
                      rfl

theorem cell22_906915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4, 5].length) (baseStart_906915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_906915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_906915 prefixEnd_906915 := by exact prefixLift 906915
  have htrace : WordTrace (prefixWord ++ tailWord_906915) baseStart_906915 baseEnd_906915 := by
    simpa [prefixWord, tailWord_906915, baseEnd_906915] using wordTrace_append hprefix tailTrace_906915
  have hstable : (prefixWord ++ tailWord_906915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906915).length < 2 ^ (prefixWord ++ tailWord_906915).sum := by decide
  have hdescent : baseEnd_906915 < baseStart_906915 := by decide
  rcases family_descends (prefixWord ++ tailWord_906915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906917 : List Nat := [1, 3, 1, 2, 1, 2, 5, 2, 5]
def baseStart_906917 : Nat := 118140960795 + 906917 * 2 ^ 59
def prefixEnd_906917 : Nat := 4983230072969 + 3 ^ 40 * 906917 * 2
def baseEnd_906917 : Nat := 103485407718607425948149

theorem tailTrace_906917 : CollatzResearch.WordTrace tailWord_906917 prefixEnd_906917 103485407718607425948149 := by
  unfold tailWord_906917
  simp only [CollatzResearch.WordTrace]
  refine ⟨33077980455402072937359005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22051986970268048624906003 33077980455402072937359005)
  ·
    refine ⟨12404242670775777351509627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33077980455402072937359005 12404242670775777351509627)
    ·
      refine ⟨18606364006163666027264441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12404242670775777351509627 18606364006163666027264441)
      ·
        refine ⟨13954773004622749520448331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18606364006163666027264441 13954773004622749520448331)
        ·
          refine ⟨20932159506934124280672497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13954773004622749520448331 20932159506934124280672497)
          ·
            refine ⟨15699119630200593210504373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20932159506934124280672497 15699119630200593210504373)
            ·
              refine ⟨1471792465331305613484785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15699119630200593210504373 1471792465331305613484785)
              ·
                refine ⟨1103844348998479210113589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1471792465331305613484785 1103844348998479210113589)
                ·
                  refine ⟨103485407718607425948149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1103844348998479210113589 103485407718607425948149)
                  ·
                    rfl

theorem cell22_906917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 2, 5].length) (baseStart_906917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_906917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_906917 prefixEnd_906917 := by exact prefixLift 906917
  have htrace : WordTrace (prefixWord ++ tailWord_906917) baseStart_906917 baseEnd_906917 := by
    simpa [prefixWord, tailWord_906917, baseEnd_906917] using wordTrace_append hprefix tailTrace_906917
  have hstable : (prefixWord ++ tailWord_906917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906917).length < 2 ^ (prefixWord ++ tailWord_906917).sum := by decide
  have hdescent : baseEnd_906917 < baseStart_906917 := by decide
  rcases family_descends (prefixWord ++ tailWord_906917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907026 : List Nat := [3, 2, 4, 1, 1, 1, 2, 2, 2, 4]
def baseStart_907026 : Nat := 118140960795 + 907026 * 2 ^ 59
def prefixEnd_907026 : Nat := 4983230072969 + 3 ^ 40 * 907026 * 2
def baseEnd_907026 : Nat := 310493536083382326869113

theorem tailTrace_907026 : CollatzResearch.WordTrace tailWord_907026 prefixEnd_907026 310493536083382326869113 := by
  unfold tailWord_907026
  simp only [CollatzResearch.WordTrace]
  refine ⟨8270489003001796138269233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22054637341338123035384621 8270489003001796138269233)
  ·
    refine ⟨6202866752251347103701925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8270489003001796138269233 6202866752251347103701925)
    ·
      refine ⟨1163037516047127581944111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6202866752251347103701925 1163037516047127581944111)
      ·
        refine ⟨1744556274070691372916167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1163037516047127581944111 1744556274070691372916167)
        ·
          refine ⟨2616834411106037059374251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1744556274070691372916167 2616834411106037059374251)
          ·
            refine ⟨3925251616659055589061377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2616834411106037059374251 3925251616659055589061377)
            ·
              refine ⟨2943938712494291691796033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3925251616659055589061377 2943938712494291691796033)
              ·
                refine ⟨2207954034370718768847025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2943938712494291691796033 2207954034370718768847025)
                ·
                  refine ⟨1655965525778039076635269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2207954034370718768847025 1655965525778039076635269)
                  ·
                    refine ⟨310493536083382326869113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1655965525778039076635269 310493536083382326869113)
                    ·
                      rfl

theorem cell22_907026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_907026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_907026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_907026 prefixEnd_907026 := by exact prefixLift 907026
  have htrace : WordTrace (prefixWord ++ tailWord_907026) baseStart_907026 baseEnd_907026 := by
    simpa [prefixWord, tailWord_907026, baseEnd_907026] using wordTrace_append hprefix tailTrace_907026
  have hstable : (prefixWord ++ tailWord_907026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907026).length < 2 ^ (prefixWord ++ tailWord_907026).sum := by decide
  have hdescent : baseEnd_907026 < baseStart_907026 := by decide
  rcases family_descends (prefixWord ++ tailWord_907026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907039 : List Nat := [1, 1, 2, 4, 2, 1, 2, 3, 3, 3]
def baseStart_907039 : Nat := 118140960795 + 907039 * 2 ^ 59
def prefixEnd_907039 : Nat := 4983230072969 + 3 ^ 40 * 907039 * 2
def baseEnd_907039 : Nat := 310497986249054626294073

theorem tailTrace_907039 : CollatzResearch.WordTrace tailWord_907039 prefixEnd_907039 310497986249054626294073 := by
  unfold tailWord_907039
  simp only [CollatzResearch.WordTrace]
  refine ⟨33082430160960087773300171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22054953440640058515533447 33082430160960087773300171)
  ·
    refine ⟨49623645241440131659950257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33082430160960087773300171 49623645241440131659950257)
    ·
      refine ⟨37217733931080098744962693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49623645241440131659950257 37217733931080098744962693)
      ·
        refine ⟨6978325112077518514680505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37217733931080098744962693 6978325112077518514680505)
        ·
          refine ⟨5233743834058138886010379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6978325112077518514680505 5233743834058138886010379)
          ·
            refine ⟨7850615751087208329015569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5233743834058138886010379 7850615751087208329015569)
            ·
              refine ⟨5887961813315406246761677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7850615751087208329015569 5887961813315406246761677)
              ·
                refine ⟨2207985679993277342535629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5887961813315406246761677 2207985679993277342535629)
                ·
                  refine ⟨827994629997479003450861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2207985679993277342535629 827994629997479003450861)
                  ·
                    refine ⟨310497986249054626294073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 827994629997479003450861 310497986249054626294073)
                    ·
                      rfl

theorem cell22_907039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3, 3, 3].length) (baseStart_907039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_907039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_907039 prefixEnd_907039 := by exact prefixLift 907039
  have htrace : WordTrace (prefixWord ++ tailWord_907039) baseStart_907039 baseEnd_907039 := by
    simpa [prefixWord, tailWord_907039, baseEnd_907039] using wordTrace_append hprefix tailTrace_907039
  have hstable : (prefixWord ++ tailWord_907039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907039).length < 2 ^ (prefixWord ++ tailWord_907039).sum := by decide
  have hdescent : baseEnd_907039 < baseStart_907039 := by decide
  rcases family_descends (prefixWord ++ tailWord_907039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907116 : List Nat := [2, 2, 1, 1, 4, 3, 2, 2, 1, 4]
def baseStart_907116 : Nat := 118140960795 + 907116 * 2 ^ 59
def prefixEnd_907116 : Nat := 4983230072969 + 3 ^ 40 * 907116 * 2
def baseEnd_907116 : Nat := 310524344922652092118837

theorem tailTrace_907116 : CollatzResearch.WordTrace tailWord_907116 prefixEnd_907116 310524344922652092118837 := by
  unfold tailWord_907116
  simp only [CollatzResearch.WordTrace]
  refine ⟨16542619290840564961926601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22056825721120753282568801 16542619290840564961926601)
  ·
    refine ⟨12406964468130423721444951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16542619290840564961926601 12406964468130423721444951)
    ·
      refine ⟨18610446702195635582167427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12406964468130423721444951 18610446702195635582167427)
      ·
        refine ⟨27915670053293453373251141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18610446702195635582167427 27915670053293453373251141)
        ·
          refine ⟨5234188134992522507484589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27915670053293453373251141 5234188134992522507484589)
          ·
            refine ⟨1962820550622195940306721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5234188134992522507484589 1962820550622195940306721)
            ·
              refine ⟨1472115412966646955230041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1962820550622195940306721 1472115412966646955230041)
              ·
                refine ⟨1104086559724985216422531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1472115412966646955230041 1104086559724985216422531)
                ·
                  refine ⟨1656129839587477824633797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1104086559724985216422531 1656129839587477824633797)
                  ·
                    refine ⟨310524344922652092118837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1656129839587477824633797 310524344922652092118837)
                    ·
                      rfl

theorem cell22_907116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 4].length) (baseStart_907116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_907116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_907116 prefixEnd_907116 := by exact prefixLift 907116
  have htrace : WordTrace (prefixWord ++ tailWord_907116) baseStart_907116 baseEnd_907116 := by
    simpa [prefixWord, tailWord_907116, baseEnd_907116] using wordTrace_append hprefix tailTrace_907116
  have hstable : (prefixWord ++ tailWord_907116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907116).length < 2 ^ (prefixWord ++ tailWord_907116).sum := by decide
  have hdescent : baseEnd_907116 < baseStart_907116 := by decide
  rcases family_descends (prefixWord ++ tailWord_907116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907129 : List Nat := [1, 2, 1, 3, 2, 2, 1, 1, 6, 3]
def baseStart_907129 : Nat := 118140960795 + 907129 * 2 ^ 59
def prefixEnd_907129 : Nat := 4983230072969 + 3 ^ 40 * 907129 * 2
def baseEnd_907129 : Nat := 310528795088324391543797

theorem tailTrace_907129 : CollatzResearch.WordTrace tailWord_907129 prefixEnd_907129 310528795088324391543797 := by
  unfold tailWord_907129
  simp only [CollatzResearch.WordTrace]
  refine ⟨33085712730634033144076441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22057141820422688762717627 33085712730634033144076441)
  ·
    refine ⟨24814284547975524858057331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33085712730634033144076441 24814284547975524858057331)
    ·
      refine ⟨37221426821963287287085997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24814284547975524858057331 37221426821963287287085997)
      ·
        refine ⟨13958035058236232732657249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37221426821963287287085997 13958035058236232732657249)
        ·
          refine ⟨10468526293677174549492937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13958035058236232732657249 10468526293677174549492937)
          ·
            refine ⟨7851394720257880912119703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10468526293677174549492937 7851394720257880912119703)
            ·
              refine ⟨11777092080386821368179555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7851394720257880912119703 11777092080386821368179555)
              ·
                refine ⟨17665638120580232052269333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11777092080386821368179555 17665638120580232052269333)
                ·
                  refine ⟨828076786902198377450125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 17665638120580232052269333 828076786902198377450125)
                  ·
                    refine ⟨310528795088324391543797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 828076786902198377450125 310528795088324391543797)
                    ·
                      rfl

theorem cell22_907129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 6, 3].length) (baseStart_907129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_907129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_907129 prefixEnd_907129 := by exact prefixLift 907129
  have htrace : WordTrace (prefixWord ++ tailWord_907129) baseStart_907129 baseEnd_907129 := by
    simpa [prefixWord, tailWord_907129, baseEnd_907129] using wordTrace_append hprefix tailTrace_907129
  have hstable : (prefixWord ++ tailWord_907129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907129).length < 2 ^ (prefixWord ++ tailWord_907129).sum := by decide
  have hdescent : baseEnd_907129 < baseStart_907129 := by decide
  rcases family_descends (prefixWord ++ tailWord_907129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907159 : List Nat := [1, 1, 3, 3, 1, 4, 2, 7]
def baseStart_907159 : Nat := 118140960795 + 907159 * 2 ^ 59
def prefixEnd_907159 : Nat := 4983230072969 + 3 ^ 40 * 907159 * 2
def baseEnd_907159 : Nat := 34504340522379368143745

theorem tailTrace_907159 : CollatzResearch.WordTrace tailWord_907159 prefixEnd_907159 34504340522379368143745 := by
  unfold tailWord_907159
  simp only [CollatzResearch.WordTrace]
  refine ⟨33086806920525348267668531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22057871280350232178445687 33086806920525348267668531)
  ·
    refine ⟨49630210380788022401502797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33086806920525348267668531 49630210380788022401502797)
    ·
      refine ⟨18611328892795508400563549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49630210380788022401502797 18611328892795508400563549)
      ·
        refine ⟨6979248334798315650211331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18611328892795508400563549 6979248334798315650211331)
        ·
          refine ⟨10468872502197473475316997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6979248334798315650211331 10468872502197473475316997)
          ·
            refine ⟨1962913594162026276621937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10468872502197473475316997 1962913594162026276621937)
            ·
              refine ⟨1472185195621519707466453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1962913594162026276621937 1472185195621519707466453)
              ·
                refine ⟨34504340522379368143745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1472185195621519707466453 34504340522379368143745)
                ·
                  rfl

theorem cell22_907159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 7].length) (baseStart_907159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_907159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_907159 prefixEnd_907159 := by exact prefixLift 907159
  have htrace : WordTrace (prefixWord ++ tailWord_907159) baseStart_907159 baseEnd_907159 := by
    simpa [prefixWord, tailWord_907159, baseEnd_907159] using wordTrace_append hprefix tailTrace_907159
  have hstable : (prefixWord ++ tailWord_907159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907159).length < 2 ^ (prefixWord ++ tailWord_907159).sum := by decide
  have hdescent : baseEnd_907159 < baseStart_907159 := by decide
  rcases family_descends (prefixWord ++ tailWord_907159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907221 : List Nat := [1, 3, 2, 3, 2, 1, 2, 3, 5]
def baseStart_907221 : Nat := 118140960795 + 907221 * 2 ^ 59
def prefixEnd_907221 : Nat := 4983230072969 + 3 ^ 40 * 907221 * 2
def baseEnd_907221 : Nat := 103520096189488939414505

theorem tailTrace_907221 : CollatzResearch.WordTrace tailWord_907221 prefixEnd_907221 103520096189488939414505 := by
  unfold tailWord_907221
  simp only [CollatzResearch.WordTrace]
  refine ⟨33089068246300732856425517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22059378830867155237617011 33089068246300732856425517)
  ·
    refine ⟨12408400592362774821159569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33089068246300732856425517 12408400592362774821159569)
    ·
      refine ⟨9306300444272081115869677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12408400592362774821159569 9306300444272081115869677)
      ·
        refine ⟨3489862666602030418451129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9306300444272081115869677 3489862666602030418451129)
        ·
          refine ⟨2617396999951522813838347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3489862666602030418451129 2617396999951522813838347)
          ·
            refine ⟨3926095499927284220757521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2617396999951522813838347 3926095499927284220757521)
            ·
              refine ⟨2944571624945463165568141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3926095499927284220757521 2944571624945463165568141)
              ·
                refine ⟨1104214359354548687088053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2944571624945463165568141 1104214359354548687088053)
                ·
                  refine ⟨103520096189488939414505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1104214359354548687088053 103520096189488939414505)
                  ·
                    rfl

theorem cell22_907221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 3, 5].length) (baseStart_907221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_907221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_907221 prefixEnd_907221 := by exact prefixLift 907221
  have htrace : WordTrace (prefixWord ++ tailWord_907221) baseStart_907221 baseEnd_907221 := by
    simpa [prefixWord, tailWord_907221, baseEnd_907221] using wordTrace_append hprefix tailTrace_907221
  have hstable : (prefixWord ++ tailWord_907221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907221).length < 2 ^ (prefixWord ++ tailWord_907221).sum := by decide
  have hdescent : baseEnd_907221 < baseStart_907221 := by decide
  rcases family_descends (prefixWord ++ tailWord_907221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907373 : List Nat := [1, 5, 1, 1, 2, 1, 4, 2, 5]
def baseStart_907373 : Nat := 118140960795 + 907373 * 2 ^ 59
def prefixEnd_907373 : Nat := 4983230072969 + 3 ^ 40 * 907373 * 2
def baseEnd_907373 : Nat := 103537440424929696147683

theorem tailTrace_907373 : CollatzResearch.WordTrace tailWord_907373 prefixEnd_907373 103537440424929696147683 := by
  unfold tailWord_907373
  simp only [CollatzResearch.WordTrace]
  refine ⟨33094612141750062815958773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22063074761166708543972515 33094612141750062815958773)
  ·
    refine ⟨3102619888289068388996135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33094612141750062815958773 3102619888289068388996135)
    ·
      refine ⟨4653929832433602583494203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3102619888289068388996135 4653929832433602583494203)
      ·
        refine ⟨6980894748650403875241305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4653929832433602583494203 6980894748650403875241305)
        ·
          refine ⟨5235671061487802906430979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6980894748650403875241305 5235671061487802906430979)
          ·
            refine ⟨7853506592231704359646469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5235671061487802906430979 7853506592231704359646469)
            ·
              refine ⟨1472532486043444567433713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7853506592231704359646469 1472532486043444567433713)
              ·
                refine ⟨1104399364532583425575285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1472532486043444567433713 1104399364532583425575285)
                ·
                  refine ⟨103537440424929696147683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1104399364532583425575285 103537440424929696147683)
                  ·
                    rfl

theorem cell22_907373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_907373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_907373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_907373 prefixEnd_907373 := by exact prefixLift 907373
  have htrace : WordTrace (prefixWord ++ tailWord_907373) baseStart_907373 baseEnd_907373 := by
    simpa [prefixWord, tailWord_907373, baseEnd_907373] using wordTrace_append hprefix tailTrace_907373
  have hstable : (prefixWord ++ tailWord_907373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907373).length < 2 ^ (prefixWord ++ tailWord_907373).sum := by decide
  have hdescent : baseEnd_907373 < baseStart_907373 := by decide
  rcases family_descends (prefixWord ++ tailWord_907373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907401 : List Nat := [1, 2, 1, 1, 4, 2, 3, 2, 6]
def baseStart_907401 : Nat := 118140960795 + 907401 * 2 ^ 59
def prefixEnd_907401 : Nat := 4983230072969 + 3 ^ 40 * 907401 * 2
def baseEnd_907401 : Nat := 103540635415668782914321

theorem tailTrace_907401 : CollatzResearch.WordTrace tailWord_907401 prefixEnd_907401 103540635415668782914321 := by
  unfold tailWord_907401
  simp only [CollatzResearch.WordTrace]
  refine ⟨33095633385648623597978057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22063755590432415731985371 33095633385648623597978057)
  ·
    refine ⟨24821725039236467698483543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33095633385648623597978057 24821725039236467698483543)
    ·
      refine ⟨37232587558854701547725315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24821725039236467698483543 37232587558854701547725315)
      ·
        refine ⟨55848881338282052321587973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37232587558854701547725315 55848881338282052321587973)
        ·
          refine ⟨10471665250927884810297745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55848881338282052321587973 10471665250927884810297745)
          ·
            refine ⟨7853748938195913607723309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10471665250927884810297745 7853748938195913607723309)
            ·
              refine ⟨2945155851823467602896241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7853748938195913607723309 2945155851823467602896241)
              ·
                refine ⟨2208866888867600702172181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2945155851823467602896241 2208866888867600702172181)
                ·
                  refine ⟨103540635415668782914321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2208866888867600702172181 103540635415668782914321)
                  ·
                    rfl

theorem cell22_907401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2, 6].length) (baseStart_907401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_907401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_907401 prefixEnd_907401 := by exact prefixLift 907401
  have htrace : WordTrace (prefixWord ++ tailWord_907401) baseStart_907401 baseEnd_907401 := by
    simpa [prefixWord, tailWord_907401, baseEnd_907401] using wordTrace_append hprefix tailTrace_907401
  have hstable : (prefixWord ++ tailWord_907401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907401).length < 2 ^ (prefixWord ++ tailWord_907401).sum := by decide
  have hdescent : baseEnd_907401 < baseStart_907401 := by decide
  rcases family_descends (prefixWord ++ tailWord_907401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907501 : List Nat := [1, 5, 1, 2, 4, 1, 2, 1, 2, 3]
def baseStart_907501 : Nat := 118140960795 + 907501 * 2 ^ 59
def prefixEnd_907501 : Nat := 4983230072969 + 3 ^ 40 * 907501 * 2
def baseEnd_907501 : Nat := 310656138290639421242657

theorem tailTrace_907501 : CollatzResearch.WordTrace tailWord_907501 prefixEnd_907501 310656138290639421242657 := by
  unfold tailWord_907501
  simp only [CollatzResearch.WordTrace]
  refine ⟨33099280685286340676618357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22066187123524227117745571 33099280685286340676618357)
  ·
    refine ⟨3103057564245594438432971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33099280685286340676618357 3103057564245594438432971)
    ·
      refine ⟨4654586346368391657649457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3103057564245594438432971 4654586346368391657649457)
      ·
        refine ⟨3490939759776293743237093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4654586346368391657649457 3490939759776293743237093)
        ·
          refine ⟨654551204958055076856955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3490939759776293743237093 654551204958055076856955)
          ·
            refine ⟨981826807437082615285433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 654551204958055076856955 981826807437082615285433)
            ·
              refine ⟨736370105577811961464075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 981826807437082615285433 736370105577811961464075)
              ·
                refine ⟨1104555158366717942196113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 736370105577811961464075 1104555158366717942196113)
                ·
                  refine ⟨828416368775038456647085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1104555158366717942196113 828416368775038456647085)
                  ·
                    refine ⟨310656138290639421242657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 828416368775038456647085 310656138290639421242657)
                    ·
                      rfl

theorem cell22_907501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_907501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_907501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_907501 prefixEnd_907501 := by exact prefixLift 907501
  have htrace : WordTrace (prefixWord ++ tailWord_907501) baseStart_907501 baseEnd_907501 := by
    simpa [prefixWord, tailWord_907501, baseEnd_907501] using wordTrace_append hprefix tailTrace_907501
  have hstable : (prefixWord ++ tailWord_907501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907501).length < 2 ^ (prefixWord ++ tailWord_907501).sum := by decide
  have hdescent : baseEnd_907501 < baseStart_907501 := by decide
  rcases family_descends (prefixWord ++ tailWord_907501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907546 : List Nat := [3, 1, 1, 3, 4, 2, 2, 2, 1, 3]
def baseStart_907546 : Nat := 118140960795 + 907546 * 2 ^ 59
def prefixEnd_907546 : Nat := 4983230072969 + 3 ^ 40 * 907546 * 2
def baseEnd_907546 : Nat := 310671542710274303867519

theorem tailTrace_907546 : CollatzResearch.WordTrace tailWord_907546 prefixEnd_907546 310671542710274303867519 := by
  unfold tailWord_907546
  simp only [CollatzResearch.WordTrace]
  refine ⟨8275230492530828340501623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22067281313415542241337661 8275230492530828340501623)
  ·
    refine ⟨12412845738796242510752435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8275230492530828340501623 12412845738796242510752435)
    ·
      refine ⟨18619268608194363766128653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12412845738796242510752435 18619268608194363766128653)
      ·
        refine ⟨6982225728072886412298245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18619268608194363766128653 6982225728072886412298245)
        ·
          refine ⟨1309167324013666202305921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6982225728072886412298245 1309167324013666202305921)
          ·
            refine ⟨981875493010249651729441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1309167324013666202305921 981875493010249651729441)
            ·
              refine ⟨736406619757687238797081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 981875493010249651729441 736406619757687238797081)
              ·
                refine ⟨552304964818265429097811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 736406619757687238797081 552304964818265429097811)
                ·
                  refine ⟨828457447227398143646717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 552304964818265429097811 828457447227398143646717)
                  ·
                    refine ⟨310671542710274303867519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 828457447227398143646717 310671542710274303867519)
                    ·
                      rfl

theorem cell22_907546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 2, 1, 3].length) (baseStart_907546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_907546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_907546 prefixEnd_907546 := by exact prefixLift 907546
  have htrace : WordTrace (prefixWord ++ tailWord_907546) baseStart_907546 baseEnd_907546 := by
    simpa [prefixWord, tailWord_907546, baseEnd_907546] using wordTrace_append hprefix tailTrace_907546
  have hstable : (prefixWord ++ tailWord_907546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907546).length < 2 ^ (prefixWord ++ tailWord_907546).sum := by decide
  have hdescent : baseEnd_907546 < baseStart_907546 := by decide
  rcases family_descends (prefixWord ++ tailWord_907546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907570 : List Nat := [3, 2, 1, 1, 5, 1, 1, 2, 6]
def baseStart_907570 : Nat := 118140960795 + 907570 * 2 ^ 59
def prefixEnd_907570 : Nat := 4983230072969 + 3 ^ 40 * 907570 * 2
def baseEnd_907570 : Nat := 103559919466915413755815

theorem tailTrace_907570 : CollatzResearch.WordTrace tailWord_907570 prefixEnd_907570 103559919466915413755815 := by
  unfold tailWord_907570
  simp only [CollatzResearch.WordTrace]
  refine ⟨8275449330509091365220041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22067864881357576973920109 8275449330509091365220041)
  ·
    refine ⟨6206586997881818523915031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8275449330509091365220041 6206586997881818523915031)
    ·
      refine ⟨9309880496822727785872547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6206586997881818523915031 9309880496822727785872547)
      ·
        refine ⟨13964820745234091678808821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9309880496822727785872547 13964820745234091678808821)
        ·
          refine ⟨1309201944865696094888327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13964820745234091678808821 1309201944865696094888327)
          ·
            refine ⟨1963802917298544142332491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1309201944865696094888327 1963802917298544142332491)
            ·
              refine ⟨2945704375947816213498737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1963802917298544142332491 2945704375947816213498737)
              ·
                refine ⟨2209278281960862160124053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2945704375947816213498737 2209278281960862160124053)
                ·
                  refine ⟨103559919466915413755815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2209278281960862160124053 103559919466915413755815)
                  ·
                    rfl

theorem cell22_907570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 2, 6].length) (baseStart_907570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_907570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_907570 prefixEnd_907570 := by exact prefixLift 907570
  have htrace : WordTrace (prefixWord ++ tailWord_907570) baseStart_907570 baseEnd_907570 := by
    simpa [prefixWord, tailWord_907570, baseEnd_907570] using wordTrace_append hprefix tailTrace_907570
  have hstable : (prefixWord ++ tailWord_907570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907570).length < 2 ^ (prefixWord ++ tailWord_907570).sum := by decide
  have hdescent : baseEnd_907570 < baseStart_907570 := by decide
  rcases family_descends (prefixWord ++ tailWord_907570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907583 : List Nat := [1, 1, 2, 2, 4, 1, 3, 1, 1, 6]
def baseStart_907583 : Nat := 118140960795 + 907583 * 2 ^ 59
def prefixEnd_907583 : Nat := 4983230072969 + 3 ^ 40 * 907583 * 2
def baseEnd_907583 : Nat := 310684208566418540692405

theorem tailTrace_907583 : CollatzResearch.WordTrace tailWord_907583 prefixEnd_907583 310684208566418540692405 := by
  unfold tailWord_907583
  simp only [CollatzResearch.WordTrace]
  refine ⟨33102271470989268681103403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22068180980659512454068935 33102271470989268681103403)
  ·
    refine ⟨49653407206483903021655105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33102271470989268681103403 49653407206483903021655105)
    ·
      refine ⟨37240055404862927266241329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49653407206483903021655105 37240055404862927266241329)
      ·
        refine ⟨27930041553647195449680997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37240055404862927266241329 27930041553647195449680997)
        ·
          refine ⟨5236882791308849146815187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27930041553647195449680997 5236882791308849146815187)
          ·
            refine ⟨7855324186963273720222781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5236882791308849146815187 7855324186963273720222781)
            ·
              refine ⟨2945746570111227645083543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7855324186963273720222781 2945746570111227645083543)
              ·
                refine ⟨4418619855166841467625315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2945746570111227645083543 4418619855166841467625315)
                ·
                  refine ⟨6627929782750262201437973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4418619855166841467625315 6627929782750262201437973)
                  ·
                    refine ⟨310684208566418540692405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6627929782750262201437973 310684208566418540692405)
                    ·
                      rfl

theorem cell22_907583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 6].length) (baseStart_907583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_907583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_907583 prefixEnd_907583 := by exact prefixLift 907583
  have htrace : WordTrace (prefixWord ++ tailWord_907583) baseStart_907583 baseEnd_907583 := by
    simpa [prefixWord, tailWord_907583, baseEnd_907583] using wordTrace_append hprefix tailTrace_907583
  have hstable : (prefixWord ++ tailWord_907583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907583).length < 2 ^ (prefixWord ++ tailWord_907583).sum := by decide
  have hdescent : baseEnd_907583 < baseStart_907583 := by decide
  rcases family_descends (prefixWord ++ tailWord_907583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907602 : List Nat := [3, 2, 2, 1, 1, 1, 5, 2, 2, 3]
def baseStart_907602 : Nat := 118140960795 + 907602 * 2 ^ 59
def prefixEnd_907602 : Nat := 4983230072969 + 3 ^ 40 * 907602 * 2
def baseEnd_907602 : Nat := 310690712654708824467347

theorem tailTrace_907602 : CollatzResearch.WordTrace tailWord_907602 prefixEnd_907602 310690712654708824467347 := by
  unfold tailWord_907602
  simp only [CollatzResearch.WordTrace]
  refine ⟨8275741114480108731511265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22068642971946956617363373 8275741114480108731511265)
  ·
    refine ⟨6206805835860081548633449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8275741114480108731511265 6206805835860081548633449)
    ·
      refine ⟨4655104376895061161475087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6206805835860081548633449 4655104376895061161475087)
      ·
        refine ⟨6982656565342591742212631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4655104376895061161475087 6982656565342591742212631)
        ·
          refine ⟨10473984848013887613318947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6982656565342591742212631 10473984848013887613318947)
          ·
            refine ⟨15710977272020831419978421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10473984848013887613318947 15710977272020831419978421)
            ·
              refine ⟨1472904119251952945622977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15710977272020831419978421 1472904119251952945622977)
              ·
                refine ⟨1104678089438964709217233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1472904119251952945622977 1104678089438964709217233)
                ·
                  refine ⟨828508567079223531912925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1104678089438964709217233 828508567079223531912925)
                  ·
                    refine ⟨310690712654708824467347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 828508567079223531912925 310690712654708824467347)
                    ·
                      rfl

theorem cell22_907602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_907602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_907602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_907602 prefixEnd_907602 := by exact prefixLift 907602
  have htrace : WordTrace (prefixWord ++ tailWord_907602) baseStart_907602 baseEnd_907602 := by
    simpa [prefixWord, tailWord_907602, baseEnd_907602] using wordTrace_append hprefix tailTrace_907602
  have hstable : (prefixWord ++ tailWord_907602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907602).length < 2 ^ (prefixWord ++ tailWord_907602).sum := by decide
  have hdescent : baseEnd_907602 < baseStart_907602 := by decide
  rcases family_descends (prefixWord ++ tailWord_907602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907638 : List Nat := [5, 1, 1, 4, 2, 1, 1, 3, 4]
def baseStart_907638 : Nat := 118140960795 + 907638 * 2 ^ 59
def prefixEnd_907638 : Nat := 4983230072969 + 3 ^ 40 * 907638 * 2
def baseEnd_907638 : Nat := 103567678730138910189079

theorem tailTrace_907638 : CollatzResearch.WordTrace tailWord_907638 prefixEnd_907638 103567678730138910189079 := by
  unfold tailWord_907638
  simp only [CollatzResearch.WordTrace]
  refine ⟨2069017342861875817147223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22069518323860008716237045 2069017342861875817147223)
  ·
    refine ⟨3103526014292813725720835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2069017342861875817147223 3103526014292813725720835)
    ·
      refine ⟨4655289021439220588581253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3103526014292813725720835 4655289021439220588581253)
      ·
        refine ⟨872866691519853860358985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4655289021439220588581253 872866691519853860358985)
        ·
          refine ⟨654650018639890395269239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 872866691519853860358985 654650018639890395269239)
          ·
            refine ⟨981975027959835592903859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 654650018639890395269239 981975027959835592903859)
            ·
              refine ⟨1472962541939753389355789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 981975027959835592903859 1472962541939753389355789)
              ·
                refine ⟨552360953227407521008421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1472962541939753389355789 552360953227407521008421)
                ·
                  refine ⟨103567678730138910189079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 552360953227407521008421 103567678730138910189079)
                  ·
                    rfl

theorem cell22_907638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_907638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_907638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_907638 prefixEnd_907638 := by exact prefixLift 907638
  have htrace : WordTrace (prefixWord ++ tailWord_907638) baseStart_907638 baseEnd_907638 := by
    simpa [prefixWord, tailWord_907638, baseEnd_907638] using wordTrace_append hprefix tailTrace_907638
  have hstable : (prefixWord ++ tailWord_907638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907638).length < 2 ^ (prefixWord ++ tailWord_907638).sum := by decide
  have hdescent : baseEnd_907638 < baseStart_907638 := by decide
  rcases family_descends (prefixWord ++ tailWord_907638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907643 : List Nat := [1, 1, 1, 1, 1, 7, 1, 2, 7]
def baseStart_907643 : Nat := 118140960795 + 907643 * 2 ^ 59
def prefixEnd_907643 : Nat := 4983230072969 + 3 ^ 40 * 907643 * 2
def baseEnd_907643 : Nat := 103568249264199461397407

theorem tailTrace_907643 : CollatzResearch.WordTrace tailWord_907643 prefixEnd_907643 103568249264199461397407 := by
  unfold tailWord_907643
  simp only [CollatzResearch.WordTrace]
  refine ⟨33104459850771898928287583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22069639900514599285525055 33104459850771898928287583)
  ·
    refine ⟨49656689776157848392431375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33104459850771898928287583 49656689776157848392431375)
    ·
      refine ⟨74485034664236772588647063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49656689776157848392431375 74485034664236772588647063)
      ·
        refine ⟨111727551996355158882970595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74485034664236772588647063 111727551996355158882970595)
        ·
          refine ⟨167591327994532738324455893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111727551996355158882970595 167591327994532738324455893)
          ·
            refine ⟨3927921749871861054479435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 167591327994532738324455893 3927921749871861054479435)
            ·
              refine ⟨5891882624807791581719153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3927921749871861054479435 5891882624807791581719153)
              ·
                refine ⟨4418911968605843686289365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5891882624807791581719153 4418911968605843686289365)
                ·
                  refine ⟨103568249264199461397407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4418911968605843686289365 103568249264199461397407)
                  ·
                    rfl

theorem cell22_907643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 7].length) (baseStart_907643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_907643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_907643 prefixEnd_907643 := by exact prefixLift 907643
  have htrace : WordTrace (prefixWord ++ tailWord_907643) baseStart_907643 baseEnd_907643 := by
    simpa [prefixWord, tailWord_907643, baseEnd_907643] using wordTrace_append hprefix tailTrace_907643
  have hstable : (prefixWord ++ tailWord_907643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907643).length < 2 ^ (prefixWord ++ tailWord_907643).sum := by decide
  have hdescent : baseEnd_907643 < baseStart_907643 := by decide
  rcases family_descends (prefixWord ++ tailWord_907643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907677 : List Nat := [1, 4, 2, 1, 4, 1, 1, 3, 5]
def baseStart_907677 : Nat := 118140960795 + 907677 * 2 ^ 59
def prefixEnd_907677 : Nat := 4983230072969 + 3 ^ 40 * 907677 * 2
def baseEnd_907677 : Nat := 103572128895811209614039

theorem tailTrace_907677 : CollatzResearch.WordTrace tailWord_907677 prefixEnd_907677 103572128895811209614039 := by
  unfold tailWord_907677
  simp only [CollatzResearch.WordTrace]
  refine ⟨33105699932648722735025285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22070466621765815156683523 33105699932648722735025285)
  ·
    refine ⟨6207318737371635512817241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33105699932648722735025285 6207318737371635512817241)
    ·
      refine ⟨4655489053028726634612931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6207318737371635512817241 4655489053028726634612931)
      ·
        refine ⟨6983233579543089951919397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4655489053028726634612931 6983233579543089951919397)
        ·
          refine ⟨1309356296164329365984887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6983233579543089951919397 1309356296164329365984887)
          ·
            refine ⟨1964034444246494048977331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1309356296164329365984887 1964034444246494048977331)
            ·
              refine ⟨2946051666369741073465997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1964034444246494048977331 2946051666369741073465997)
              ·
                refine ⟨1104769374888652902549749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2946051666369741073465997 1104769374888652902549749)
                ·
                  refine ⟨103572128895811209614039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1104769374888652902549749 103572128895811209614039)
                  ·
                    rfl

theorem cell22_907677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 3, 5].length) (baseStart_907677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_907677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_907677 prefixEnd_907677 := by exact prefixLift 907677
  have htrace : WordTrace (prefixWord ++ tailWord_907677) baseStart_907677 baseEnd_907677 := by
    simpa [prefixWord, tailWord_907677, baseEnd_907677] using wordTrace_append hprefix tailTrace_907677
  have hstable : (prefixWord ++ tailWord_907677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907677).length < 2 ^ (prefixWord ++ tailWord_907677).sum := by decide
  have hdescent : baseEnd_907677 < baseStart_907677 := by decide
  rcases family_descends (prefixWord ++ tailWord_907677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907722 : List Nat := [3, 1, 2, 1, 2, 2, 3, 4, 4]
def baseStart_907722 : Nat := 118140960795 + 907722 * 2 ^ 59
def prefixEnd_907722 : Nat := 4983230072969 + 3 ^ 40 * 907722 * 2
def baseEnd_907722 : Nat := 103577263702356170488993

theorem tailTrace_907722 : CollatzResearch.WordTrace tailWord_907722 prefixEnd_907722 103577263702356170488993 := by
  unfold tailWord_907722
  simp only [CollatzResearch.WordTrace]
  refine ⟨8276835304371423855103355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22071560811657130280275613 8276835304371423855103355)
  ·
    refine ⟨12415252956557135782655033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8276835304371423855103355 12415252956557135782655033)
    ·
      refine ⟨9311439717417851836991275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12415252956557135782655033 9311439717417851836991275)
      ·
        refine ⟨13967159576126777755486913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9311439717417851836991275 13967159576126777755486913)
        ·
          refine ⟨10475369682095083316615185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13967159576126777755486913 10475369682095083316615185)
          ·
            refine ⟨7856527261571312487461389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10475369682095083316615185 7856527261571312487461389)
            ·
              refine ⟨2946197723089242182798021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7856527261571312487461389 2946197723089242182798021)
              ·
                refine ⟨552412073079232909274629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2946197723089242182798021 552412073079232909274629)
                ·
                  refine ⟨103577263702356170488993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 552412073079232909274629 103577263702356170488993)
                  ·
                    rfl

theorem cell22_907722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 4, 4].length) (baseStart_907722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_907722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_907722 prefixEnd_907722 := by exact prefixLift 907722
  have htrace : WordTrace (prefixWord ++ tailWord_907722) baseStart_907722 baseEnd_907722 := by
    simpa [prefixWord, tailWord_907722, baseEnd_907722] using wordTrace_append hprefix tailTrace_907722
  have hstable : (prefixWord ++ tailWord_907722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907722).length < 2 ^ (prefixWord ++ tailWord_907722).sum := by decide
  have hdescent : baseEnd_907722 < baseStart_907722 := by decide
  rcases family_descends (prefixWord ++ tailWord_907722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907737 : List Nat := [1, 2, 1, 2, 4, 1, 1, 5, 2, 3]
def baseStart_907737 : Nat := 118140960795 + 907737 * 2 ^ 59
def prefixEnd_907737 : Nat := 4983230072969 + 3 ^ 40 * 907737 * 2
def baseEnd_907737 : Nat := 310736925913613472341933

theorem tailTrace_907737 : CollatzResearch.WordTrace tailWord_907737 prefixEnd_907737 310736925913613472341933 := by
  unfold tailWord_907737
  simp only [CollatzResearch.WordTrace]
  refine ⟨33107888312431352982209465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22071925541620901988139643 33107888312431352982209465)
  ·
    refine ⟨24830916234323514736657099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33107888312431352982209465 24830916234323514736657099)
    ·
      refine ⟨37246374351485272104985649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24830916234323514736657099 37246374351485272104985649)
      ·
        refine ⟨27934780763613954078739237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37246374351485272104985649 27934780763613954078739237)
        ·
          refine ⟨5237771393177616389763607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27934780763613954078739237 5237771393177616389763607)
          ·
            refine ⟨7856657089766424584645411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5237771393177616389763607 7856657089766424584645411)
            ·
              refine ⟨11784985634649636876968117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7856657089766424584645411 11784985634649636876968117)
              ·
                refine ⟨1104842403248403457215761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11784985634649636876968117 1104842403248403457215761)
                ·
                  refine ⟨828631802436302592911821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1104842403248403457215761 828631802436302592911821)
                  ·
                    refine ⟨310736925913613472341933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 828631802436302592911821 310736925913613472341933)
                    ·
                      rfl

theorem cell22_907737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 5, 2, 3].length) (baseStart_907737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_907737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_907737 prefixEnd_907737 := by exact prefixLift 907737
  have htrace : WordTrace (prefixWord ++ tailWord_907737) baseStart_907737 baseEnd_907737 := by
    simpa [prefixWord, tailWord_907737, baseEnd_907737] using wordTrace_append hprefix tailTrace_907737
  have hstable : (prefixWord ++ tailWord_907737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907737).length < 2 ^ (prefixWord ++ tailWord_907737).sum := by decide
  have hdescent : baseEnd_907737 < baseStart_907737 := by decide
  rcases family_descends (prefixWord ++ tailWord_907737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907752 : List Nat := [2, 1, 4, 1, 1, 3, 3, 1, 2, 4]
def baseStart_907752 : Nat := 118140960795 + 907752 * 2 ^ 59
def prefixEnd_907752 : Nat := 4983230072969 + 3 ^ 40 * 907752 * 2
def baseEnd_907752 : Nat := 310742060720158433216887

theorem tailTrace_907752 : CollatzResearch.WordTrace tailWord_907752 prefixEnd_907752 310742060720158433216887 := by
  unfold tailWord_907752
  simp only [CollatzResearch.WordTrace]
  refine ⟨16554217703688505272002755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22072290271584673696003673 16554217703688505272002755)
  ·
    refine ⟨24831326555532757908004133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16554217703688505272002755 24831326555532757908004133)
    ·
      refine ⟨4655873729162392107750775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24831326555532757908004133 4655873729162392107750775)
      ·
        refine ⟨6983810593743588161626163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4655873729162392107750775 6983810593743588161626163)
        ·
          refine ⟨10475715890615382242439245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6983810593743588161626163 10475715890615382242439245)
          ·
            refine ⟨3928393458980768340914717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10475715890615382242439245 3928393458980768340914717)
            ·
              refine ⟨1473147547117788127843019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3928393458980768340914717 1473147547117788127843019)
              ·
                refine ⟨2209721320676682191764529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1473147547117788127843019 2209721320676682191764529)
                ·
                  refine ⟨1657290990507511643823397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2209721320676682191764529 1657290990507511643823397)
                  ·
                    refine ⟨310742060720158433216887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1657290990507511643823397 310742060720158433216887)
                    ·
                      rfl

theorem cell22_907752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_907752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_907752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_907752 prefixEnd_907752 := by exact prefixLift 907752
  have htrace : WordTrace (prefixWord ++ tailWord_907752) baseStart_907752 baseEnd_907752 := by
    simpa [prefixWord, tailWord_907752, baseEnd_907752] using wordTrace_append hprefix tailTrace_907752
  have hstable : (prefixWord ++ tailWord_907752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907752).length < 2 ^ (prefixWord ++ tailWord_907752).sum := by decide
  have hdescent : baseEnd_907752 < baseStart_907752 := by decide
  rcases family_descends (prefixWord ++ tailWord_907752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907846 : List Nat := [6, 1, 1, 1, 2, 2, 1, 3, 5]
def baseStart_907846 : Nat := 118140960795 + 907846 * 2 ^ 59
def prefixEnd_907846 : Nat := 4983230072969 + 3 ^ 40 * 907846 * 2
def baseEnd_907846 : Nat := 103591412947057840455533

theorem tailTrace_907846 : CollatzResearch.WordTrace tailWord_907846 prefixEnd_907846 103591412947057840455533 := by
  unfold tailWord_907846
  simp only [CollatzResearch.WordTrace]
  refine ⟨1034745745907389518685231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22074575912690976398618261 1034745745907389518685231)
  ·
    refine ⟨1552118618861084278027847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1034745745907389518685231 1552118618861084278027847)
    ·
      refine ⟨2328177928291626417041771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1552118618861084278027847 2328177928291626417041771)
      ·
        refine ⟨3492266892437439625562657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2328177928291626417041771 3492266892437439625562657)
        ·
          refine ⟨2619200169328079719171993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3492266892437439625562657 2619200169328079719171993)
          ·
            refine ⟨1964400126996059789378995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2619200169328079719171993 1964400126996059789378995)
            ·
              refine ⟨2946600190494089684068493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1964400126996059789378995 2946600190494089684068493)
              ·
                refine ⟨1104975071435283631525685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2946600190494089684068493 1104975071435283631525685)
                ·
                  refine ⟨103591412947057840455533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1104975071435283631525685 103591412947057840455533)
                  ·
                    rfl

theorem cell22_907846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_907846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_907846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_907846 prefixEnd_907846 := by exact prefixLift 907846
  have htrace : WordTrace (prefixWord ++ tailWord_907846) baseStart_907846 baseEnd_907846 := by
    simpa [prefixWord, tailWord_907846, baseEnd_907846] using wordTrace_append hprefix tailTrace_907846
  have hstable : (prefixWord ++ tailWord_907846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907846).length < 2 ^ (prefixWord ++ tailWord_907846).sum := by decide
  have hdescent : baseEnd_907846 < baseStart_907846 := by decide
  rcases family_descends (prefixWord ++ tailWord_907846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907872 : List Nat := [2, 1, 1, 3, 2, 1, 2, 1, 6, 3]
def baseStart_907872 : Nat := 118140960795 + 907872 * 2 ^ 59
def prefixEnd_907872 : Nat := 4983230072969 + 3 ^ 40 * 907872 * 2
def baseEnd_907872 : Nat := 310783139172518120216519

theorem tailTrace_907872 : CollatzResearch.WordTrace tailWord_907872 prefixEnd_907872 310783139172518120216519 := by
  unfold tailWord_907872
  simp only [CollatzResearch.WordTrace]
  refine ⟨16556406083471135519186935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22075208111294847358915913 16556406083471135519186935)
  ·
    refine ⟨24834609125206703278780403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16556406083471135519186935 24834609125206703278780403)
    ·
      refine ⟨37251913687810054918170605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24834609125206703278780403 37251913687810054918170605)
      ·
        refine ⟨13969467632928770594313977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37251913687810054918170605 13969467632928770594313977)
        ·
          refine ⟨10477100724696577945735483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13969467632928770594313977 10477100724696577945735483)
          ·
            refine ⟨15715651087044866918603225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10477100724696577945735483 15715651087044866918603225)
            ·
              refine ⟨11786738315283650188952419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15715651087044866918603225 11786738315283650188952419)
              ·
                refine ⟨17680107472925475283428629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11786738315283650188952419 17680107472925475283428629)
                ·
                  refine ⟨828755037793381653910717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 17680107472925475283428629 828755037793381653910717)
                  ·
                    refine ⟨310783139172518120216519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 828755037793381653910717 310783139172518120216519)
                    ·
                      rfl

theorem cell22_907872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 6, 3].length) (baseStart_907872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_907872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_907872 prefixEnd_907872 := by exact prefixLift 907872
  have htrace : WordTrace (prefixWord ++ tailWord_907872) baseStart_907872 baseEnd_907872 := by
    simpa [prefixWord, tailWord_907872, baseEnd_907872] using wordTrace_append hprefix tailTrace_907872
  have hstable : (prefixWord ++ tailWord_907872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907872).length < 2 ^ (prefixWord ++ tailWord_907872).sum := by decide
  have hdescent : baseEnd_907872 < baseStart_907872 := by decide
  rcases family_descends (prefixWord ++ tailWord_907872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907887 : List Nat := [1, 1, 2, 1, 3, 2, 4, 2, 2, 4]
def baseStart_907887 : Nat := 118140960795 + 907887 * 2 ^ 59
def prefixEnd_907887 : Nat := 4983230072969 + 3 ^ 40 * 907887 * 2
def baseEnd_907887 : Nat := 310788273979063081091473

theorem tailTrace_907887 : CollatzResearch.WordTrace tailWord_907887 prefixEnd_907887 310788273979063081091473 := by
  unfold tailWord_907887
  simp only [CollatzResearch.WordTrace]
  refine ⟨33113359261887928600169915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22075572841258619066779943 33113359261887928600169915)
  ·
    refine ⟨49670038892831892900254873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33113359261887928600169915 49670038892831892900254873)
    ·
      refine ⟨37252529169623919675191155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49670038892831892900254873 37252529169623919675191155)
      ·
        refine ⟨55878793754435879512786733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37252529169623919675191155 55878793754435879512786733)
        ·
          refine ⟨20954547657913454817295025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55878793754435879512786733 20954547657913454817295025)
          ·
            refine ⟨15715910743435091112971269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20954547657913454817295025 15715910743435091112971269)
            ·
              refine ⟨2946733264394079583682113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15715910743435091112971269 2946733264394079583682113)
              ·
                refine ⟨2210049948295559687761585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2946733264394079583682113 2210049948295559687761585)
                ·
                  refine ⟨1657537461221669765821189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2210049948295559687761585 1657537461221669765821189)
                  ·
                    refine ⟨310788273979063081091473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1657537461221669765821189 310788273979063081091473)
                    ·
                      rfl

theorem cell22_907887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2, 2, 4].length) (baseStart_907887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_907887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_907887 prefixEnd_907887 := by exact prefixLift 907887
  have htrace : WordTrace (prefixWord ++ tailWord_907887) baseStart_907887 baseEnd_907887 := by
    simpa [prefixWord, tailWord_907887, baseEnd_907887] using wordTrace_append hprefix tailTrace_907887
  have hstable : (prefixWord ++ tailWord_907887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907887).length < 2 ^ (prefixWord ++ tailWord_907887).sum := by decide
  have hdescent : baseEnd_907887 < baseStart_907887 := by decide
  rcases family_descends (prefixWord ++ tailWord_907887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907951 : List Nat := [1, 1, 2, 1, 2, 5, 2, 4, 1, 3]
def baseStart_907951 : Nat := 118140960795 + 907951 * 2 ^ 59
def prefixEnd_907951 : Nat := 4983230072969 + 3 ^ 40 * 907951 * 2
def baseEnd_907951 : Nat := 310810182486988247491277

theorem tailTrace_907951 : CollatzResearch.WordTrace tailWord_907951 prefixEnd_907951 310810182486988247491277 := by
  unfold tailWord_907951
  simp only [CollatzResearch.WordTrace]
  refine ⟨33115693533656067530499707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22077129022437378353666471 33115693533656067530499707)
  ·
    refine ⟨49673540300484101295749561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33115693533656067530499707 49673540300484101295749561)
    ·
      refine ⟨37255155225363075971812171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49673540300484101295749561 37255155225363075971812171)
      ·
        refine ⟨55882732838044613957718257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37255155225363075971812171 55882732838044613957718257)
        ·
          refine ⟨41912049628533460468288693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55882732838044613957718257 41912049628533460468288693)
          ·
            refine ⟨3929254652675011918902065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41912049628533460468288693 3929254652675011918902065)
            ·
              refine ⟨2946940989506258939176549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3929254652675011918902065 2946940989506258939176549)
              ·
                refine ⟨552551435532423551095603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2946940989506258939176549 552551435532423551095603)
                ·
                  refine ⟨828827153298635326643405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 552551435532423551095603 828827153298635326643405)
                  ·
                    refine ⟨310810182486988247491277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 828827153298635326643405 310810182486988247491277)
                    ·
                      rfl

theorem cell22_907951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 4, 1, 3].length) (baseStart_907951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_907951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_907951 prefixEnd_907951 := by exact prefixLift 907951
  have htrace : WordTrace (prefixWord ++ tailWord_907951) baseStart_907951 baseEnd_907951 := by
    simpa [prefixWord, tailWord_907951, baseEnd_907951] using wordTrace_append hprefix tailTrace_907951
  have hstable : (prefixWord ++ tailWord_907951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907951).length < 2 ^ (prefixWord ++ tailWord_907951).sum := by decide
  have hdescent : baseEnd_907951 < baseStart_907951 := by decide
  rcases family_descends (prefixWord ++ tailWord_907951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907962 : List Nat := [3, 1, 1, 1, 2, 3, 1, 3, 2, 5]
def baseStart_907962 : Nat := 118140960795 + 907962 * 2 ^ 59
def prefixEnd_907962 : Nat := 4983230072969 + 3 ^ 40 * 907962 * 2
def baseEnd_907962 : Nat := 310813948011787885466243

theorem tailTrace_907962 : CollatzResearch.WordTrace tailWord_907962 prefixEnd_907962 310813948011787885466243 := by
  unfold tailWord_907962
  simp only [CollatzResearch.WordTrace]
  refine ⟨8279023684154054102287535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22077396491077477606100093 8279023684154054102287535)
  ·
    refine ⟨12418535526231081153431303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8279023684154054102287535 12418535526231081153431303)
    ·
      refine ⟨18627803289346621730146955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12418535526231081153431303 18627803289346621730146955)
      ·
        refine ⟨27941704934019932595220433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18627803289346621730146955 27941704934019932595220433)
        ·
          refine ⟨20956278700514949446415325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27941704934019932595220433 20956278700514949446415325)
          ·
            refine ⟨7858604512693106042405747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20956278700514949446415325 7858604512693106042405747)
            ·
              refine ⟨11787906769039659063608621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7858604512693106042405747 11787906769039659063608621)
              ·
                refine ⟨4420465038389872148853233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11787906769039659063608621 4420465038389872148853233)
                ·
                  refine ⟨3315348778792404111639925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4420465038389872148853233 3315348778792404111639925)
                  ·
                    refine ⟨310813948011787885466243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3315348778792404111639925 310813948011787885466243)
                    ·
                      rfl

theorem cell22_907962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 2, 5].length) (baseStart_907962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_907962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_907962 prefixEnd_907962 := by exact prefixLift 907962
  have htrace : WordTrace (prefixWord ++ tailWord_907962) baseStart_907962 baseEnd_907962 := by
    simpa [prefixWord, tailWord_907962, baseEnd_907962] using wordTrace_append hprefix tailTrace_907962
  have hstable : (prefixWord ++ tailWord_907962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907962).length < 2 ^ (prefixWord ++ tailWord_907962).sum := by decide
  have hdescent : baseEnd_907962 < baseStart_907962 := by decide
  rcases family_descends (prefixWord ++ tailWord_907962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907994 : List Nat := [3, 1, 1, 2, 2, 2, 1, 5, 1, 4]
def baseStart_907994 : Nat := 118140960795 + 907994 * 2 ^ 59
def prefixEnd_907994 : Nat := 4983230072969 + 3 ^ 40 * 907994 * 2
def baseEnd_907994 : Nat := 310824902265750468666145

theorem tailTrace_907994 : CollatzResearch.WordTrace tailWord_907994 prefixEnd_907994 310824902265750468666145 := by
  unfold tailWord_907994
  simp only [CollatzResearch.WordTrace]
  refine ⟨8279315468125071468578759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22078174581666857249543357 8279315468125071468578759)
  ·
    refine ⟨12418973202187607202868139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8279315468125071468578759 12418973202187607202868139)
    ·
      refine ⟨18628459803281410804302209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12418973202187607202868139 18628459803281410804302209)
      ·
        refine ⟨13971344852461058103226657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18628459803281410804302209 13971344852461058103226657)
        ·
          refine ⟨10478508639345793577419993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13971344852461058103226657 10478508639345793577419993)
          ·
            refine ⟨7858881479509345183064995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10478508639345793577419993 7858881479509345183064995)
            ·
              refine ⟨11788322219264017774597493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7858881479509345183064995 11788322219264017774597493)
              ·
                refine ⟨1105155208056001666368515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11788322219264017774597493 1105155208056001666368515)
                ·
                  refine ⟨1657732812084002499552773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1105155208056001666368515 1657732812084002499552773)
                  ·
                    refine ⟨310824902265750468666145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1657732812084002499552773 310824902265750468666145)
                    ·
                      rfl

theorem cell22_907994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 5, 1, 4].length) (baseStart_907994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_907994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_907994 prefixEnd_907994 := by exact prefixLift 907994
  have htrace : WordTrace (prefixWord ++ tailWord_907994) baseStart_907994 baseEnd_907994 := by
    simpa [prefixWord, tailWord_907994, baseEnd_907994] using wordTrace_append hprefix tailTrace_907994
  have hstable : (prefixWord ++ tailWord_907994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907994).length < 2 ^ (prefixWord ++ tailWord_907994).sum := by decide
  have hdescent : baseEnd_907994 < baseStart_907994 := by decide
  rcases family_descends (prefixWord ++ tailWord_907994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908009 : List Nat := [1, 2, 1, 1, 1, 2, 4, 6, 4]
def baseStart_908009 : Nat := 118140960795 + 908009 * 2 ^ 59
def prefixEnd_908009 : Nat := 4983230072969 + 3 ^ 40 * 908009 * 2
def baseEnd_908009 : Nat := 103610012357431809847033

theorem tailTrace_908009 : CollatzResearch.WordTrace tailWord_908009 prefixEnd_908009 103610012357431809847033 := by
  unfold tailWord_908009
  simp only [CollatzResearch.WordTrace]
  refine ⟨33117808967445943436111081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22078539311630628957407387 33117808967445943436111081)
  ·
    refine ⟨24838356725584457577083311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33117808967445943436111081 24838356725584457577083311)
    ·
      refine ⟨37257535088376686365624967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24838356725584457577083311 37257535088376686365624967)
      ·
        refine ⟨55886302632565029548437451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37257535088376686365624967 55886302632565029548437451)
        ·
          refine ⟨83829453948847544322656177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55886302632565029548437451 83829453948847544322656177)
          ·
            refine ⟨62872090461635658241992133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83829453948847544322656177 62872090461635658241992133)
            ·
              refine ⟨11788516961556685920373525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62872090461635658241992133 11788516961556685920373525)
              ·
                refine ⟨552586732572969652517509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11788516961556685920373525 552586732572969652517509)
                ·
                  refine ⟨103610012357431809847033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 552586732572969652517509 103610012357431809847033)
                  ·
                    rfl

theorem cell22_908009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 6, 4].length) (baseStart_908009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_908009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_908009 prefixEnd_908009 := by exact prefixLift 908009
  have htrace : WordTrace (prefixWord ++ tailWord_908009) baseStart_908009 baseEnd_908009 := by
    simpa [prefixWord, tailWord_908009, baseEnd_908009] using wordTrace_append hprefix tailTrace_908009
  have hstable : (prefixWord ++ tailWord_908009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908009).length < 2 ^ (prefixWord ++ tailWord_908009).sum := by decide
  have hdescent : baseEnd_908009 < baseStart_908009 := by decide
  rcases family_descends (prefixWord ++ tailWord_908009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908114 : List Nat := [3, 2, 2, 1, 1, 2, 1, 1, 4, 5]
def baseStart_908114 : Nat := 118140960795 + 908114 * 2 ^ 59
def prefixEnd_908114 : Nat := 4983230072969 + 3 ^ 40 * 908114 * 2
def baseEnd_908114 : Nat := 310865980718110155665777

theorem tailTrace_908114 : CollatzResearch.WordTrace tailWord_908114 prefixEnd_908114 310865980718110155665777 := by
  unfold tailWord_908114
  simp only [CollatzResearch.WordTrace]
  refine ⟨8280409658016386592170849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22081092421377030912455597 8280409658016386592170849)
  ·
    refine ⟨6210307243512289944128137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8280409658016386592170849 6210307243512289944128137)
    ·
      refine ⟨4657730432634217458096103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6210307243512289944128137 4657730432634217458096103)
      ·
        refine ⟨6986595648951326187144155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4657730432634217458096103 6986595648951326187144155)
        ·
          refine ⟨10479893473426989280716233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6986595648951326187144155 10479893473426989280716233)
          ·
            refine ⟨7859920105070241960537175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10479893473426989280716233 7859920105070241960537175)
            ·
              refine ⟨11789880157605362940805763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7859920105070241960537175 11789880157605362940805763)
              ·
                refine ⟨17684820236408044411208645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11789880157605362940805763 17684820236408044411208645)
                ·
                  refine ⟨3315903794326508327101621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17684820236408044411208645 3315903794326508327101621)
                  ·
                    refine ⟨310865980718110155665777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3315903794326508327101621 310865980718110155665777)
                    ·
                      rfl

theorem cell22_908114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_908114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_908114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_908114 prefixEnd_908114 := by exact prefixLift 908114
  have htrace : WordTrace (prefixWord ++ tailWord_908114) baseStart_908114 baseEnd_908114 := by
    simpa [prefixWord, tailWord_908114, baseEnd_908114] using wordTrace_append hprefix tailTrace_908114
  have hstable : (prefixWord ++ tailWord_908114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908114).length < 2 ^ (prefixWord ++ tailWord_908114).sum := by decide
  have hdescent : baseEnd_908114 < baseStart_908114 := by decide
  rcases family_descends (prefixWord ++ tailWord_908114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908116 : List Nat := [2, 4, 1, 1, 4, 1, 1, 1, 7]
def baseStart_908116 : Nat := 118140960795 + 908116 * 2 ^ 59
def prefixEnd_908116 : Nat := 4983230072969 + 3 ^ 40 * 908116 * 2
def baseEnd_908116 : Nat := 103622221786327605705257

theorem tailTrace_908116 : CollatzResearch.WordTrace tailWord_908116 prefixEnd_908116 103622221786327605705257 := by
  unfold tailWord_908116
  simp only [CollatzResearch.WordTrace]
  refine ⟨16560855789029150355128101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22081141052038867140170801 16560855789029150355128101)
  ·
    refine ⟨3105160460442965691586519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16560855789029150355128101 3105160460442965691586519)
    ·
      refine ⟨4657740690664448537379779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3105160460442965691586519 4657740690664448537379779)
      ·
        refine ⟨6986611035996672806069669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4657740690664448537379779 6986611035996672806069669)
        ·
          refine ⟨1309989569249376151138063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6986611035996672806069669 1309989569249376151138063)
          ·
            refine ⟨1964984353874064226707095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1309989569249376151138063 1964984353874064226707095)
            ·
              refine ⟨2947476530811096340060643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1964984353874064226707095 2947476530811096340060643)
              ·
                refine ⟨4421214796216644510090965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2947476530811096340060643 4421214796216644510090965)
                ·
                  refine ⟨103622221786327605705257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4421214796216644510090965 103622221786327605705257)
                  ·
                    rfl

theorem cell22_908116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_908116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_908116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_908116 prefixEnd_908116 := by exact prefixLift 908116
  have htrace : WordTrace (prefixWord ++ tailWord_908116) baseStart_908116 baseEnd_908116 := by
    simpa [prefixWord, tailWord_908116, baseEnd_908116] using wordTrace_append hprefix tailTrace_908116
  have hstable : (prefixWord ++ tailWord_908116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908116).length < 2 ^ (prefixWord ++ tailWord_908116).sum := by decide
  have hdescent : baseEnd_908116 < baseStart_908116 := by decide
  rcases family_descends (prefixWord ++ tailWord_908116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908129 : List Nat := [1, 2, 3, 1, 1, 1, 2, 4, 3, 4]
def baseStart_908129 : Nat := 118140960795 + 908129 * 2 ^ 59
def prefixEnd_908129 : Nat := 4983230072969 + 3 ^ 40 * 908129 * 2
def baseEnd_908129 : Nat := 310871115524655116540731

theorem tailTrace_908129 : CollatzResearch.WordTrace tailWord_908129 prefixEnd_908129 310871115524655116540731 := by
  unfold tailWord_908129
  simp only [CollatzResearch.WordTrace]
  refine ⟨33122185727011203930479441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22081457151340802620319627 33122185727011203930479441)
  ·
    refine ⟨24841639295258402947859581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33122185727011203930479441 24841639295258402947859581)
    ·
      refine ⟨9315614735721901105447343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24841639295258402947859581 9315614735721901105447343)
      ·
        refine ⟨13973422103582851658171015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9315614735721901105447343 13973422103582851658171015)
        ·
          refine ⟨20960133155374277487256523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13973422103582851658171015 20960133155374277487256523)
          ·
            refine ⟨31440199733061416230884785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20960133155374277487256523 31440199733061416230884785)
            ·
              refine ⟨23580149799796062173163589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31440199733061416230884785 23580149799796062173163589)
              ·
                refine ⟨4421278087461761657468173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23580149799796062173163589 4421278087461761657468173)
                ·
                  refine ⟨1657979282798160621550565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4421278087461761657468173 1657979282798160621550565)
                  ·
                    refine ⟨310871115524655116540731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1657979282798160621550565 310871115524655116540731)
                    ·
                      rfl

theorem cell22_908129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_908129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_908129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_908129 prefixEnd_908129 := by exact prefixLift 908129
  have htrace : WordTrace (prefixWord ++ tailWord_908129) baseStart_908129 baseEnd_908129 := by
    simpa [prefixWord, tailWord_908129, baseEnd_908129] using wordTrace_append hprefix tailTrace_908129
  have hstable : (prefixWord ++ tailWord_908129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908129).length < 2 ^ (prefixWord ++ tailWord_908129).sum := by decide
  have hdescent : baseEnd_908129 < baseStart_908129 := by decide
  rcases family_descends (prefixWord ++ tailWord_908129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908144 : List Nat := [2, 1, 1, 1, 4, 1, 4, 2, 6]
def baseStart_908144 : Nat := 118140960795 + 908144 * 2 ^ 59
def prefixEnd_908144 : Nat := 4983230072969 + 3 ^ 40 * 908144 * 2
def baseEnd_908144 : Nat := 103625416777066692471895

theorem tailTrace_908144 : CollatzResearch.WordTrace tailWord_908144 prefixEnd_908144 103625416777066692471895 := by
  unfold tailWord_908144
  simp only [CollatzResearch.WordTrace]
  refine ⟨16561366410978430746137743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22081821881304574328183657 16561366410978430746137743)
  ·
    refine ⟨24842049616467646119206615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16561366410978430746137743 24842049616467646119206615)
    ·
      refine ⟨37263074424701469178809923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24842049616467646119206615 37263074424701469178809923)
      ·
        refine ⟨55894611637052203768214885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37263074424701469178809923 55894611637052203768214885)
        ·
          refine ⟨10480239681947288206540291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55894611637052203768214885 10480239681947288206540291)
          ·
            refine ⟨15720359522920932309810437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10480239681947288206540291 15720359522920932309810437)
            ·
              refine ⟨2947567410547674808089457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15720359522920932309810437 2947567410547674808089457)
              ·
                refine ⟨2210675557910756106067093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2947567410547674808089457 2210675557910756106067093)
                ·
                  refine ⟨103625416777066692471895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2210675557910756106067093 103625416777066692471895)
                  ·
                    rfl

theorem cell22_908144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2, 6].length) (baseStart_908144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_908144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_908144 prefixEnd_908144 := by exact prefixLift 908144
  have htrace : WordTrace (prefixWord ++ tailWord_908144) baseStart_908144 baseEnd_908144 := by
    simpa [prefixWord, tailWord_908144, baseEnd_908144] using wordTrace_append hprefix tailTrace_908144
  have hstable : (prefixWord ++ tailWord_908144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908144).length < 2 ^ (prefixWord ++ tailWord_908144).sum := by decide
  have hdescent : baseEnd_908144 < baseStart_908144 := by decide
  rcases family_descends (prefixWord ++ tailWord_908144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908146 : List Nat := [3, 2, 1, 2, 1, 1, 3, 4, 1, 4]
def baseStart_908146 : Nat := 118140960795 + 908146 * 2 ^ 59
def prefixEnd_908146 : Nat := 4983230072969 + 3 ^ 40 * 908146 * 2
def baseEnd_908146 : Nat := 310876934972072738865679

theorem tailTrace_908146 : CollatzResearch.WordTrace tailWord_908146 prefixEnd_908146 310876934972072738865679 := by
  unfold tailWord_908146
  simp only [CollatzResearch.WordTrace]
  refine ⟨8280701441987403958462073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22081870511966410555898861 8280701441987403958462073)
  ·
    refine ⟨6210526081490552968846555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8280701441987403958462073 6210526081490552968846555)
    ·
      refine ⟨9315789122235829453269833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6210526081490552968846555 9315789122235829453269833)
      ·
        refine ⟨6986841841676872089952375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9315789122235829453269833 6986841841676872089952375)
        ·
          refine ⟨10480262762515308134928563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6986841841676872089952375 10480262762515308134928563)
          ·
            refine ⟨15720394143772962202392845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10480262762515308134928563 15720394143772962202392845)
            ·
              refine ⟨5895147803914860825897317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15720394143772962202392845 5895147803914860825897317)
              ·
                refine ⟨1105340213234036404855747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5895147803914860825897317 1105340213234036404855747)
                ·
                  refine ⟨1658010319851054607283621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1105340213234036404855747 1658010319851054607283621)
                  ·
                    refine ⟨310876934972072738865679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1658010319851054607283621 310876934972072738865679)
                    ·
                      rfl

theorem cell22_908146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 4, 1, 4].length) (baseStart_908146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_908146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_908146 prefixEnd_908146 := by exact prefixLift 908146
  have htrace : WordTrace (prefixWord ++ tailWord_908146) baseStart_908146 baseEnd_908146 := by
    simpa [prefixWord, tailWord_908146, baseEnd_908146] using wordTrace_append hprefix tailTrace_908146
  have hstable : (prefixWord ++ tailWord_908146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908146).length < 2 ^ (prefixWord ++ tailWord_908146).sum := by decide
  have hdescent : baseEnd_908146 < baseStart_908146 := by decide
  rcases family_descends (prefixWord ++ tailWord_908146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908159 : List Nat := [1, 1, 2, 2, 1, 1, 4, 4, 1, 5]
def baseStart_908159 : Nat := 118140960795 + 908159 * 2 ^ 59
def prefixEnd_908159 : Nat := 4983230072969 + 3 ^ 40 * 908159 * 2
def baseEnd_908159 : Nat := 310881385137745038290639

theorem tailTrace_908159 : CollatzResearch.WordTrace tailWord_908159 prefixEnd_908159 310881385137745038290639 := by
  unfold tailWord_908159
  simp only [CollatzResearch.WordTrace]
  refine ⟨33123279916902519054071531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22082186611268346036047687 33123279916902519054071531)
  ·
    refine ⟨49684919875353778581107297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33123279916902519054071531 49684919875353778581107297)
    ·
      refine ⟨37263689906515333935830473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49684919875353778581107297 37263689906515333935830473)
      ·
        refine ⟨27947767429886500451872855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37263689906515333935830473 27947767429886500451872855)
        ·
          refine ⟨41921651144829750677809283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27947767429886500451872855 41921651144829750677809283)
          ·
            refine ⟨62882476717244626016713925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41921651144829750677809283 62882476717244626016713925)
            ·
              refine ⟨11790464384483367378133861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62882476717244626016713925 11790464384483367378133861)
              ·
                refine ⟨2210712072090631383400099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11790464384483367378133861 2210712072090631383400099)
                ·
                  refine ⟨3316068108135947075100149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2210712072090631383400099 3316068108135947075100149)
                  ·
                    refine ⟨310881385137745038290639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3316068108135947075100149 310881385137745038290639)
                    ·
                      rfl

theorem cell22_908159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4, 1, 5].length) (baseStart_908159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_908159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_908159 prefixEnd_908159 := by exact prefixLift 908159
  have htrace : WordTrace (prefixWord ++ tailWord_908159) baseStart_908159 baseEnd_908159 := by
    simpa [prefixWord, tailWord_908159, baseEnd_908159] using wordTrace_append hprefix tailTrace_908159
  have hstable : (prefixWord ++ tailWord_908159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908159).length < 2 ^ (prefixWord ++ tailWord_908159).sum := by decide
  have hdescent : baseEnd_908159 < baseStart_908159 := by decide
  rcases family_descends (prefixWord ++ tailWord_908159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908296 : List Nat := [2, 1, 3, 2, 1, 3, 1, 3, 6]
def baseStart_908296 : Nat := 118140960795 + 908296 * 2 ^ 59
def prefixEnd_908296 : Nat := 4983230072969 + 3 ^ 40 * 908296 * 2
def baseEnd_908296 : Nat := 103642761012507449205073

theorem tailTrace_908296 : CollatzResearch.WordTrace tailWord_908296 prefixEnd_908296 103642761012507449205073 := by
  unfold tailWord_908296
  simp only [CollatzResearch.WordTrace]
  refine ⟨16564138358703095725904371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22085517811604127634539161 16564138358703095725904371)
  ·
    refine ⟨24846207538054643588856557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16564138358703095725904371 24846207538054643588856557)
    ·
      refine ⟨9317327826770491345821209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24846207538054643588856557 9317327826770491345821209)
      ·
        refine ⟨6987995870077868509365907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9317327826770491345821209 6987995870077868509365907)
        ·
          refine ⟨10481993805116802764048861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6987995870077868509365907 10481993805116802764048861)
          ·
            refine ⟨3930747676918801036518323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10481993805116802764048861 3930747676918801036518323)
            ·
              refine ⟨5896121515378201554777485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3930747676918801036518323 5896121515378201554777485)
              ·
                refine ⟨2211045568266825583041557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5896121515378201554777485 2211045568266825583041557)
                ·
                  refine ⟨103642761012507449205073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2211045568266825583041557 103642761012507449205073)
                  ·
                    rfl

theorem cell22_908296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3, 6].length) (baseStart_908296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_908296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_908296 prefixEnd_908296 := by exact prefixLift 908296
  have htrace : WordTrace (prefixWord ++ tailWord_908296) baseStart_908296 baseEnd_908296 := by
    simpa [prefixWord, tailWord_908296, baseEnd_908296] using wordTrace_append hprefix tailTrace_908296
  have hstable : (prefixWord ++ tailWord_908296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908296).length < 2 ^ (prefixWord ++ tailWord_908296).sum := by decide
  have hdescent : baseEnd_908296 < baseStart_908296 := by decide
  rcases family_descends (prefixWord ++ tailWord_908296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908373 : List Nat := [1, 3, 2, 2, 1, 2, 2, 1, 5, 3]
def baseStart_908373 : Nat := 118140960795 + 908373 * 2 ^ 59
def prefixEnd_908373 : Nat := 4983230072969 + 3 ^ 40 * 908373 * 2
def baseEnd_908373 : Nat := 310954641711119813439983

theorem tailTrace_908373 : CollatzResearch.WordTrace tailWord_908373 prefixEnd_908373 310954641711119813439983 := by
  unfold tailWord_908373
  simp only [CollatzResearch.WordTrace]
  refine ⟨33131085138127233602361773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22087390092084822401574515 33131085138127233602361773)
  ·
    refine ⟨12424156926797712600885665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33131085138127233602361773 12424156926797712600885665)
    ·
      refine ⟨9318117695098284450664249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12424156926797712600885665 9318117695098284450664249)
      ·
        refine ⟨6988588271323713337998187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9318117695098284450664249 6988588271323713337998187)
        ·
          refine ⟨10482882406985570006997281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6988588271323713337998187 10482882406985570006997281)
          ·
            refine ⟨7862161805239177505247961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10482882406985570006997281 7862161805239177505247961)
            ·
              refine ⟨5896621353929383128935971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7862161805239177505247961 5896621353929383128935971)
              ·
                refine ⟨8844932030894074693403957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5896621353929383128935971 8844932030894074693403957)
                ·
                  refine ⟨829212377896319502506621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8844932030894074693403957 829212377896319502506621)
                  ·
                    refine ⟨310954641711119813439983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 829212377896319502506621 310954641711119813439983)
                    ·
                      rfl

theorem cell22_908373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 5, 3].length) (baseStart_908373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_908373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_908373 prefixEnd_908373 := by exact prefixLift 908373
  have htrace : WordTrace (prefixWord ++ tailWord_908373) baseStart_908373 baseEnd_908373 := by
    simpa [prefixWord, tailWord_908373, baseEnd_908373] using wordTrace_append hprefix tailTrace_908373
  have hstable : (prefixWord ++ tailWord_908373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908373).length < 2 ^ (prefixWord ++ tailWord_908373).sum := by decide
  have hdescent : baseEnd_908373 < baseStart_908373 := by decide
  rcases family_descends (prefixWord ++ tailWord_908373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908465 : List Nat := [1, 2, 2, 5, 1, 2, 2, 1, 6]
def baseStart_908465 : Nat := 118140960795 + 908465 * 2 ^ 59
def prefixEnd_908465 : Nat := 4983230072969 + 3 ^ 40 * 908465 * 2
def baseEnd_908465 : Nat := 103662045063754080046567

theorem tailTrace_908465 : CollatzResearch.WordTrace tailWord_908465 prefixEnd_908465 103662045063754080046567 := by
  unfold tailWord_908465
  simp only [CollatzResearch.WordTrace]
  refine ⟨33134440653793933314710849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22089627102529288876473899 33134440653793933314710849)
  ·
    refine ⟨24850830490345449986033137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33134440653793933314710849 24850830490345449986033137)
    ·
      refine ⟨18638122867759087489524853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24850830490345449986033137 18638122867759087489524853)
      ·
        refine ⟨1747324018852414452142955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18638122867759087489524853 1747324018852414452142955)
        ·
          refine ⟨2620986028278621678214433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1747324018852414452142955 2620986028278621678214433)
          ·
            refine ⟨1965739521208966258660825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2620986028278621678214433 1965739521208966258660825)
            ·
              refine ⟨1474304640906724693995619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1965739521208966258660825 1474304640906724693995619)
              ·
                refine ⟨2211456961360087040993429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1474304640906724693995619 2211456961360087040993429)
                ·
                  refine ⟨103662045063754080046567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2211456961360087040993429 103662045063754080046567)
                  ·
                    rfl

theorem cell22_908465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 1, 6].length) (baseStart_908465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_908465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_908465 prefixEnd_908465 := by exact prefixLift 908465
  have htrace : WordTrace (prefixWord ++ tailWord_908465) baseStart_908465 baseEnd_908465 := by
    simpa [prefixWord, tailWord_908465, baseEnd_908465] using wordTrace_append hprefix tailTrace_908465
  have hstable : (prefixWord ++ tailWord_908465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908465).length < 2 ^ (prefixWord ++ tailWord_908465).sum := by decide
  have hdescent : baseEnd_908465 < baseStart_908465 := by decide
  rcases family_descends (prefixWord ++ tailWord_908465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908615 : List Nat := [1, 1, 4, 1, 2, 3, 2, 2, 1, 5]
def baseStart_908615 : Nat := 118140960795 + 908615 * 2 ^ 59
def prefixEnd_908615 : Nat := 4983230072969 + 3 ^ 40 * 908615 * 2
def baseEnd_908615 : Nat := 311037483256711848889241

theorem tailTrace_908615 : CollatzResearch.WordTrace tailWord_908615 prefixEnd_908615 311037483256711848889241 := by
  unfold tailWord_908615
  simp only [CollatzResearch.WordTrace]
  refine ⟨33139911603250508932671299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22093274402167005955114199 33139911603250508932671299)
  ·
    refine ⟨49709867404875763399006949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33139911603250508932671299 49709867404875763399006949)
    ·
      refine ⟨9320600138414205637313803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49709867404875763399006949 9320600138414205637313803)
      ·
        refine ⟨13980900207621308455970705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9320600138414205637313803 13980900207621308455970705)
        ·
          refine ⟨10485675155715981341978029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13980900207621308455970705 10485675155715981341978029)
          ·
            refine ⟨3932128183393493003241761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10485675155715981341978029 3932128183393493003241761)
            ·
              refine ⟨2949096137545119752431321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3932128183393493003241761 2949096137545119752431321)
              ·
                refine ⟨2211822103158839814323491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2949096137545119752431321 2211822103158839814323491)
                ·
                  refine ⟨3317733154738259721485237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2211822103158839814323491 3317733154738259721485237)
                  ·
                    refine ⟨311037483256711848889241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3317733154738259721485237 311037483256711848889241)
                    ·
                      rfl

theorem cell22_908615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_908615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_908615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_908615 prefixEnd_908615 := by exact prefixLift 908615
  have htrace : WordTrace (prefixWord ++ tailWord_908615) baseStart_908615 baseEnd_908615 := by
    simpa [prefixWord, tailWord_908615, baseEnd_908615] using wordTrace_append hprefix tailTrace_908615
  have hstable : (prefixWord ++ tailWord_908615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908615).length < 2 ^ (prefixWord ++ tailWord_908615).sum := by decide
  have hdescent : baseEnd_908615 < baseStart_908615 := by decide
  rcases family_descends (prefixWord ++ tailWord_908615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908700 : List Nat := [2, 2, 3, 4, 2, 1, 2, 1, 2, 3]
def baseStart_908700 : Nat := 118140960795 + 908700 * 2 ^ 59
def prefixEnd_908700 : Nat := 4983230072969 + 3 ^ 40 * 908700 * 2
def baseEnd_908700 : Nat := 311066580493799960513981

theorem tailTrace_908700 : CollatzResearch.WordTrace tailWord_908700 prefixEnd_908700 311066580493799960513981 := by
  unfold tailWord_908700
  simp only [CollatzResearch.WordTrace]
  refine ⟨16571505903971284224757777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22095341205295045633010369 16571505903971284224757777)
  ·
    refine ⟨12428629427978463168568333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16571505903971284224757777 12428629427978463168568333)
    ·
      refine ⟨4660736035491923688213125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12428629427978463168568333 4660736035491923688213125)
      ·
        refine ⟨873888006654735691539961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4660736035491923688213125 873888006654735691539961)
        ·
          refine ⟨655416004991051768654971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 873888006654735691539961 655416004991051768654971)
          ·
            refine ⟨983124007486577652982457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 655416004991051768654971 983124007486577652982457)
            ·
              refine ⟨737343005614933239736843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 983124007486577652982457 737343005614933239736843)
              ·
                refine ⟨1106014508422399859605265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 737343005614933239736843 1106014508422399859605265)
                ·
                  refine ⟨829510881316799894703949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1106014508422399859605265 829510881316799894703949)
                  ·
                    refine ⟨311066580493799960513981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 829510881316799894703949 311066580493799960513981)
                    ·
                      rfl

theorem cell22_908700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_908700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_908700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_908700 prefixEnd_908700 := by exact prefixLift 908700
  have htrace : WordTrace (prefixWord ++ tailWord_908700) baseStart_908700 baseEnd_908700 := by
    simpa [prefixWord, tailWord_908700, baseEnd_908700] using wordTrace_append hprefix tailTrace_908700
  have hstable : (prefixWord ++ tailWord_908700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908700).length < 2 ^ (prefixWord ++ tailWord_908700).sum := by decide
  have hdescent : baseEnd_908700 < baseStart_908700 := by decide
  rcases family_descends (prefixWord ++ tailWord_908700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908752 : List Nat := [2, 1, 1, 1, 1, 2, 2, 8, 4]
def baseStart_908752 : Nat := 118140960795 + 908752 * 2 ^ 59
def prefixEnd_908752 : Nat := 4983230072969 + 3 ^ 40 * 908752 * 2
def baseEnd_908752 : Nat := 103694793718829719404607

theorem tailTrace_908752 : CollatzResearch.WordTrace tailWord_908752 prefixEnd_908752 103694793718829719404607 := by
  unfold tailWord_908752
  simp only [CollatzResearch.WordTrace]
  refine ⟨16572454201877090665204255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22096605602502787553605673 16572454201877090665204255)
  ·
    refine ⟨24858681302815635997806383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16572454201877090665204255 24858681302815635997806383)
    ·
      refine ⟨37288021954223453996709575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24858681302815635997806383 37288021954223453996709575)
      ·
        refine ⟨55932032931335180995064363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37288021954223453996709575 55932032931335180995064363)
        ·
          refine ⟨83898049397002771492596545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55932032931335180995064363 83898049397002771492596545)
          ·
            refine ⟨62923537047752078619447409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83898049397002771492596545 62923537047752078619447409)
            ·
              refine ⟨47192652785814058964585557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62923537047752078619447409 47192652785814058964585557)
              ·
                refine ⟨553038899833758503491237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 47192652785814058964585557 553038899833758503491237)
                ·
                  refine ⟨103694793718829719404607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 553038899833758503491237 103694793718829719404607)
                  ·
                    rfl

theorem cell22_908752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 8, 4].length) (baseStart_908752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_908752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_908752 prefixEnd_908752 := by exact prefixLift 908752
  have htrace : WordTrace (prefixWord ++ tailWord_908752) baseStart_908752 baseEnd_908752 := by
    simpa [prefixWord, tailWord_908752, baseEnd_908752] using wordTrace_append hprefix tailTrace_908752
  have hstable : (prefixWord ++ tailWord_908752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908752).length < 2 ^ (prefixWord ++ tailWord_908752).sum := by decide
  have hdescent : baseEnd_908752 < baseStart_908752 := by decide
  rcases family_descends (prefixWord ++ tailWord_908752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908767 : List Nat := [1, 1, 2, 3, 3, 1, 4, 1, 1, 5]
def baseStart_908767 : Nat := 118140960795 + 908767 * 2 ^ 59
def prefixEnd_908767 : Nat := 4983230072969 + 3 ^ 40 * 908767 * 2
def baseEnd_908767 : Nat := 311089515963034119088775

theorem tailTrace_908767 : CollatzResearch.WordTrace tailWord_908767 prefixEnd_908767 311089515963034119088775 := by
  unfold tailWord_908767
  simp only [CollatzResearch.WordTrace]
  refine ⟨33145455498699838892204555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22096970332466559261469703 33145455498699838892204555)
  ·
    refine ⟨49718183248049758338306833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33145455498699838892204555 49718183248049758338306833)
    ·
      refine ⟨37288637436037318753730125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49718183248049758338306833 37288637436037318753730125)
      ·
        refine ⟨13983239038513994532648797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37288637436037318753730125 13983239038513994532648797)
        ·
          refine ⟨5243714639442747949743299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13983239038513994532648797 5243714639442747949743299)
          ·
            refine ⟨7865571959164121924614949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5243714639442747949743299 7865571959164121924614949)
            ·
              refine ⟨1474794742343272860865303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7865571959164121924614949 1474794742343272860865303)
              ·
                refine ⟨2212192113514909291297955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1474794742343272860865303 2212192113514909291297955)
                ·
                  refine ⟨3318288170272363936946933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2212192113514909291297955 3318288170272363936946933)
                  ·
                    refine ⟨311089515963034119088775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3318288170272363936946933 311089515963034119088775)
                    ·
                      rfl

theorem cell22_908767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 1, 1, 5].length) (baseStart_908767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_908767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_908767 prefixEnd_908767 := by exact prefixLift 908767
  have htrace : WordTrace (prefixWord ++ tailWord_908767) baseStart_908767 baseEnd_908767 := by
    simpa [prefixWord, tailWord_908767, baseEnd_908767] using wordTrace_append hprefix tailTrace_908767
  have hstable : (prefixWord ++ tailWord_908767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908767).length < 2 ^ (prefixWord ++ tailWord_908767).sum := by decide
  have hdescent : baseEnd_908767 < baseStart_908767 := by decide
  rcases family_descends (prefixWord ++ tailWord_908767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908782 : List Nat := [4, 1, 2, 1, 2, 1, 3, 1, 1, 6]
def baseStart_908782 : Nat := 118140960795 + 908782 * 2 ^ 59
def prefixEnd_908782 : Nat := 4983230072969 + 3 ^ 40 * 908782 * 2
def baseEnd_908782 : Nat := 311094650769579079963729

theorem tailTrace_908782 : CollatzResearch.WordTrace tailWord_908782 prefixEnd_908782 311094650769579079963729 := by
  unfold tailWord_908782
  simp only [CollatzResearch.WordTrace]
  refine ⟨4143250324205687056750075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22097335062430330969333733 4143250324205687056750075)
  ·
    refine ⟨6214875486308530585125113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4143250324205687056750075 6214875486308530585125113)
    ·
      refine ⟨4661156614731397938843835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6214875486308530585125113 4661156614731397938843835)
      ·
        refine ⟨6991734922097096908265753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4661156614731397938843835 6991734922097096908265753)
        ·
          refine ⟨5243801191572822681199315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6991734922097096908265753 5243801191572822681199315)
          ·
            refine ⟨7865701787359234021798973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5243801191572822681199315 7865701787359234021798973)
            ·
              refine ⟨2949638170259712758174615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7865701787359234021798973 2949638170259712758174615)
              ·
                refine ⟨4424457255389569137261923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2949638170259712758174615 4424457255389569137261923)
                ·
                  refine ⟨6636685883084353705892885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4424457255389569137261923 6636685883084353705892885)
                  ·
                    refine ⟨311094650769579079963729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6636685883084353705892885 311094650769579079963729)
                    ·
                      rfl

theorem cell22_908782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_908782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_908782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_908782 prefixEnd_908782 := by exact prefixLift 908782
  have htrace : WordTrace (prefixWord ++ tailWord_908782) baseStart_908782 baseEnd_908782 := by
    simpa [prefixWord, tailWord_908782, baseEnd_908782] using wordTrace_append hprefix tailTrace_908782
  have hstable : (prefixWord ++ tailWord_908782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908782).length < 2 ^ (prefixWord ++ tailWord_908782).sum := by decide
  have hdescent : baseEnd_908782 < baseStart_908782 := by decide
  rcases family_descends (prefixWord ++ tailWord_908782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908786 : List Nat := [3, 2, 1, 4, 1, 2, 2, 3, 4]
def baseStart_908786 : Nat := 118140960795 + 908786 * 2 ^ 59
def prefixEnd_908786 : Nat := 4983230072969 + 3 ^ 40 * 908786 * 2
def baseEnd_908786 : Nat := 103698673350441467621239

theorem tailTrace_908786 : CollatzResearch.WordTrace tailWord_908786 prefixEnd_908786 103698673350441467621239 := by
  unfold tailWord_908786
  simp only [CollatzResearch.WordTrace]
  refine ⟨8286537121407751284286553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22097432323754003424764141 8286537121407751284286553)
  ·
    refine ⟨6214902841055813463214915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8286537121407751284286553 6214902841055813463214915)
    ·
      refine ⟨9322354261583720194822373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6214902841055813463214915 9322354261583720194822373)
      ·
        refine ⟨1747941424046947536529195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9322354261583720194822373 1747941424046947536529195)
        ·
          refine ⟨2621912136070421304793793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1747941424046947536529195 2621912136070421304793793)
          ·
            refine ⟨1966434102052815978595345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2621912136070421304793793 1966434102052815978595345)
            ·
              refine ⟨1474825576539611983946509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1966434102052815978595345 1474825576539611983946509)
              ·
                refine ⟨553059591202354493979941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1474825576539611983946509 553059591202354493979941)
                ·
                  refine ⟨103698673350441467621239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 553059591202354493979941 103698673350441467621239)
                  ·
                    rfl

theorem cell22_908786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 3, 4].length) (baseStart_908786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_908786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_908786 prefixEnd_908786 := by exact prefixLift 908786
  have htrace : WordTrace (prefixWord ++ tailWord_908786) baseStart_908786 baseEnd_908786 := by
    simpa [prefixWord, tailWord_908786, baseEnd_908786] using wordTrace_append hprefix tailTrace_908786
  have hstable : (prefixWord ++ tailWord_908786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908786).length < 2 ^ (prefixWord ++ tailWord_908786).sum := by decide
  have hdescent : baseEnd_908786 < baseStart_908786 := by decide
  rcases family_descends (prefixWord ++ tailWord_908786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908825 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 11]
def baseStart_908825 : Nat := 118140960795 + 908825 * 2 ^ 59
def prefixEnd_908825 : Nat := 4983230072969 + 3 ^ 40 * 908825 * 2
def baseEnd_908825 : Nat := 103703123516113767046199

theorem tailTrace_908825 : CollatzResearch.WordTrace tailWord_908825 prefixEnd_908825 103703123516113767046199 := by
  unfold tailWord_908825
  simp only [CollatzResearch.WordTrace]
  refine ⟨33147570932489714797815929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22098380621659809865210619 33147570932489714797815929)
  ·
    refine ⟨24860678199367286098361947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33147570932489714797815929 24860678199367286098361947)
    ·
      refine ⟨37291017299050929147542921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24860678199367286098361947 37291017299050929147542921)
      ·
        refine ⟨27968262974288196860657191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37291017299050929147542921 27968262974288196860657191)
        ·
          refine ⟨41952394461432295290985787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27968262974288196860657191 41952394461432295290985787)
          ·
            refine ⟨62928591692148442936478681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41952394461432295290985787 62928591692148442936478681)
            ·
              refine ⟨47196443769111332202359011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62928591692148442936478681 47196443769111332202359011)
              ·
                refine ⟨70794665653666998303538517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47196443769111332202359011 70794665653666998303538517)
                ·
                  refine ⟨103703123516113767046199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 70794665653666998303538517 103703123516113767046199)
                  ·
                    rfl

theorem cell22_908825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 11].length) (baseStart_908825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_908825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_908825 prefixEnd_908825 := by exact prefixLift 908825
  have htrace : WordTrace (prefixWord ++ tailWord_908825) baseStart_908825 baseEnd_908825 := by
    simpa [prefixWord, tailWord_908825, baseEnd_908825] using wordTrace_append hprefix tailTrace_908825
  have hstable : (prefixWord ++ tailWord_908825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908825).length < 2 ^ (prefixWord ++ tailWord_908825).sum := by decide
  have hdescent : baseEnd_908825 < baseStart_908825 := by decide
  rcases family_descends (prefixWord ++ tailWord_908825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908829 : List Nat := [1, 4, 2, 2, 1, 1, 1, 4, 3, 3]
def baseStart_908829 : Nat := 118140960795 + 908829 * 2 ^ 59
def prefixEnd_908829 : Nat := 4983230072969 + 3 ^ 40 * 908829 * 2
def baseEnd_908829 : Nat := 311110739830086624038585

theorem tailTrace_908829 : CollatzResearch.WordTrace tailWord_908829 prefixEnd_908829 311110739830086624038585 := by
  unfold tailWord_908829
  simp only [CollatzResearch.WordTrace]
  refine ⟨33147716824475223480961541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22098477882983482320641027 33147716824475223480961541)
  ·
    refine ⟨6215196904589104402680289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33147716824475223480961541 6215196904589104402680289)
    ·
      refine ⟨4661397678441828302010217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6215196904589104402680289 4661397678441828302010217)
      ·
        refine ⟨3496048258831371226507663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4661397678441828302010217 3496048258831371226507663)
        ·
          refine ⟨5244072388247056839761495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3496048258831371226507663 5244072388247056839761495)
          ·
            refine ⟨7866108582370585259642243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5244072388247056839761495 7866108582370585259642243)
            ·
              refine ⟨11799162873555877889463365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7866108582370585259642243 11799162873555877889463365)
              ·
                refine ⟨2212343038791727104274381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11799162873555877889463365 2212343038791727104274381)
                ·
                  refine ⟨829628639546897664102893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2212343038791727104274381 829628639546897664102893)
                  ·
                    refine ⟨311110739830086624038585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 829628639546897664102893 311110739830086624038585)
                    ·
                      rfl

theorem cell22_908829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_908829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_908829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_908829 prefixEnd_908829 := by exact prefixLift 908829
  have htrace : WordTrace (prefixWord ++ tailWord_908829) baseStart_908829 baseEnd_908829 := by
    simpa [prefixWord, tailWord_908829, baseEnd_908829] using wordTrace_append hprefix tailTrace_908829
  have hstable : (prefixWord ++ tailWord_908829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908829).length < 2 ^ (prefixWord ++ tailWord_908829).sum := by decide
  have hdescent : baseEnd_908829 < baseStart_908829 := by decide
  rcases family_descends (prefixWord ++ tailWord_908829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908842 : List Nat := [3, 1, 4, 1, 1, 1, 1, 1, 9]
def baseStart_908842 : Nat := 118140960795 + 908842 * 2 ^ 59
def prefixEnd_908842 : Nat := 4983230072969 + 3 ^ 40 * 908842 * 2
def baseEnd_908842 : Nat := 103705063331919641154515

theorem tailTrace_908842 : CollatzResearch.WordTrace tailWord_908842 prefixEnd_908842 103705063331919641154515 := by
  unfold tailWord_908842
  simp only [CollatzResearch.WordTrace]
  refine ⟨8287047743357031675296195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22098793982285417800789853 8287047743357031675296195)
  ·
    refine ⟨12430571615035547512944293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8287047743357031675296195 12430571615035547512944293)
    ·
      refine ⟨2330732177819165158677055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12430571615035547512944293 2330732177819165158677055)
      ·
        refine ⟨3496098266728747738015583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2330732177819165158677055 3496098266728747738015583)
        ·
          refine ⟨5244147400093121607023375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3496098266728747738015583 5244147400093121607023375)
          ·
            refine ⟨7866221100139682410535063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5244147400093121607023375 7866221100139682410535063)
            ·
              refine ⟨11799331650209523615802595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7866221100139682410535063 11799331650209523615802595)
              ·
                refine ⟨17698997475314285423703893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11799331650209523615802595 17698997475314285423703893)
                ·
                  refine ⟨103705063331919641154515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 17698997475314285423703893 103705063331919641154515)
                  ·
                    rfl

theorem cell22_908842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 9].length) (baseStart_908842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_908842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_908842 prefixEnd_908842 := by exact prefixLift 908842
  have htrace : WordTrace (prefixWord ++ tailWord_908842) baseStart_908842 baseEnd_908842 := by
    simpa [prefixWord, tailWord_908842, baseEnd_908842] using wordTrace_append hprefix tailTrace_908842
  have hstable : (prefixWord ++ tailWord_908842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908842).length < 2 ^ (prefixWord ++ tailWord_908842).sum := by decide
  have hdescent : baseEnd_908842 < baseStart_908842 := by decide
  rcases family_descends (prefixWord ++ tailWord_908842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908863 : List Nat := [1, 1, 2, 2, 3, 4, 3, 2, 1, 3]
def baseStart_908863 : Nat := 118140960795 + 908863 * 2 ^ 59
def prefixEnd_908863 : Nat := 4983230072969 + 3 ^ 40 * 908863 * 2
def baseEnd_908863 : Nat := 311122378724921868688481

theorem tailTrace_908863 : CollatzResearch.WordTrace tailWord_908863 prefixEnd_908863 311122378724921868688481 := by
  unfold tailWord_908863
  simp only [CollatzResearch.WordTrace]
  refine ⟨33148956906352047287699243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22099304604234698191799495 33148956906352047287699243)
  ·
    refine ⟨49723435359528070931548865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33148956906352047287699243 49723435359528070931548865)
    ·
      refine ⟨37292576519646053198661649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49723435359528070931548865 37292576519646053198661649)
      ·
        refine ⟨27969432389734539898996237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37292576519646053198661649 27969432389734539898996237)
        ·
          refine ⟨10488537146150452462123589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27969432389734539898996237 10488537146150452462123589)
          ·
            refine ⟨1966600714903209836648173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10488537146150452462123589 1966600714903209836648173)
            ·
              refine ⟨737475268088703688743065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1966600714903209836648173 737475268088703688743065)
              ·
                refine ⟨553106451066527766557299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 737475268088703688743065 553106451066527766557299)
                ·
                  refine ⟨829659676599791649835949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 553106451066527766557299 829659676599791649835949)
                  ·
                    refine ⟨311122378724921868688481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 829659676599791649835949 311122378724921868688481)
                    ·
                      rfl

theorem cell22_908863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 2, 1, 3].length) (baseStart_908863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_908863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_908863 prefixEnd_908863 := by exact prefixLift 908863
  have htrace : WordTrace (prefixWord ++ tailWord_908863) baseStart_908863 baseEnd_908863 := by
    simpa [prefixWord, tailWord_908863, baseEnd_908863] using wordTrace_append hprefix tailTrace_908863
  have hstable : (prefixWord ++ tailWord_908863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908863).length < 2 ^ (prefixWord ++ tailWord_908863).sum := by decide
  have hdescent : baseEnd_908863 < baseStart_908863 := by decide
  rcases family_descends (prefixWord ++ tailWord_908863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908876 : List Nat := [2, 2, 1, 3, 1, 5, 2, 1, 5]
def baseStart_908876 : Nat := 118140960795 + 908876 * 2 ^ 59
def prefixEnd_908876 : Nat := 4983230072969 + 3 ^ 40 * 908876 * 2
def baseEnd_908876 : Nat := 103708942963531389371147

theorem tailTrace_908876 : CollatzResearch.WordTrace tailWord_908876 prefixEnd_908876 103708942963531389371147 := by
  unfold tailWord_908876
  simp only [CollatzResearch.WordTrace]
  refine ⟨16574715527652475253961241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22099620703536633671948321 16574715527652475253961241)
  ·
    refine ⟨12431036645739356440470931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16574715527652475253961241 12431036645739356440470931)
    ·
      refine ⟨18646554968609034660706397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12431036645739356440470931 18646554968609034660706397)
      ·
        refine ⟨6992458113228387997764899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18646554968609034660706397 6992458113228387997764899)
        ·
          refine ⟨10488687169842581996647349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6992458113228387997764899 10488687169842581996647349)
          ·
            refine ⟨983314422172742062185689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10488687169842581996647349 983314422172742062185689)
            ·
              refine ⟨737485816629556546639267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 983314422172742062185689 737485816629556546639267)
              ·
                refine ⟨1106228724944334819958901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 737485816629556546639267 1106228724944334819958901)
                ·
                  refine ⟨103708942963531389371147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1106228724944334819958901 103708942963531389371147)
                  ·
                    rfl

theorem cell22_908876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 1, 5].length) (baseStart_908876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_908876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_908876 prefixEnd_908876 := by exact prefixLift 908876
  have htrace : WordTrace (prefixWord ++ tailWord_908876) baseStart_908876 baseEnd_908876 := by
    simpa [prefixWord, tailWord_908876, baseEnd_908876] using wordTrace_append hprefix tailTrace_908876
  have hstable : (prefixWord ++ tailWord_908876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908876).length < 2 ^ (prefixWord ++ tailWord_908876).sum := by decide
  have hdescent : baseEnd_908876 < baseStart_908876 := by decide
  rcases family_descends (prefixWord ++ tailWord_908876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908951 : List Nat := [1, 1, 3, 3, 2, 4, 1, 1, 2, 4]
def baseStart_908951 : Nat := 118140960795 + 908951 * 2 ^ 59
def prefixEnd_908951 : Nat := 4983230072969 + 3 ^ 40 * 908951 * 2
def baseEnd_908951 : Nat := 311152502923318972488211

theorem tailTrace_908951 : CollatzResearch.WordTrace tailWord_908951 prefixEnd_908951 311152502923318972488211 := by
  unfold tailWord_908951
  simp only [CollatzResearch.WordTrace]
  refine ⟨33152166530033238316902707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22101444353355492211268471 33152166530033238316902707)
  ·
    refine ⟨49728249795049857475354061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33152166530033238316902707 49728249795049857475354061)
    ·
      refine ⟨18648093673143696553257773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49728249795049857475354061 18648093673143696553257773)
      ·
        refine ⟨6993035127428886207471665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18648093673143696553257773 6993035127428886207471665)
        ·
          refine ⟨5244776345571664655603749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6993035127428886207471665 5244776345571664655603749)
          ·
            refine ⟨983395564794687122925703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5244776345571664655603749 983395564794687122925703)
            ·
              refine ⟨1475093347192030684388555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 983395564794687122925703 1475093347192030684388555)
              ·
                refine ⟨2212640020788046026582833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1475093347192030684388555 2212640020788046026582833)
                ·
                  refine ⟨1659480015591034519937125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2212640020788046026582833 1659480015591034519937125)
                  ·
                    refine ⟨311152502923318972488211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1659480015591034519937125 311152502923318972488211)
                    ·
                      rfl

theorem cell22_908951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 1, 2, 4].length) (baseStart_908951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_908951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_908951 prefixEnd_908951 := by exact prefixLift 908951
  have htrace : WordTrace (prefixWord ++ tailWord_908951) baseStart_908951 baseEnd_908951 := by
    simpa [prefixWord, tailWord_908951, baseEnd_908951] using wordTrace_append hprefix tailTrace_908951
  have hstable : (prefixWord ++ tailWord_908951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908951).length < 2 ^ (prefixWord ++ tailWord_908951).sum := by decide
  have hdescent : baseEnd_908951 < baseStart_908951 := by decide
  rcases family_descends (prefixWord ++ tailWord_908951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909007 : List Nat := [1, 1, 2, 1, 1, 3, 1, 2, 2, 8]
def baseStart_909007 : Nat := 118140960795 + 909007 * 2 ^ 59
def prefixEnd_909007 : Nat := 4983230072969 + 3 ^ 40 * 909007 * 2
def baseEnd_909007 : Nat := 311171672867753493088039

theorem tailTrace_909007 : CollatzResearch.WordTrace tailWord_909007 prefixEnd_909007 311171672867753493088039 := by
  unfold tailWord_909007
  simp only [CollatzResearch.WordTrace]
  refine ⟨33154209017830359880941275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22102806011886906587294183 33154209017830359880941275)
  ·
    refine ⟨49731313526745539821411913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33154209017830359880941275 49731313526745539821411913)
    ·
      refine ⟨37298485145059154866058935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49731313526745539821411913 37298485145059154866058935)
      ·
        refine ⟨55947727717588732299088403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37298485145059154866058935 55947727717588732299088403)
        ·
          refine ⟨83921591576383098448632605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55947727717588732299088403 83921591576383098448632605)
          ·
            refine ⟨31470596841143661918237227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83921591576383098448632605 31470596841143661918237227)
            ·
              refine ⟨47205895261715492877355841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31470596841143661918237227 47205895261715492877355841)
              ·
                refine ⟨35404421446286619658016881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47205895261715492877355841 35404421446286619658016881)
                ·
                  refine ⟨26553316084714964743512661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35404421446286619658016881 26553316084714964743512661)
                  ·
                    refine ⟨311171672867753493088039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 26553316084714964743512661 311171672867753493088039)
                    ·
                      rfl

theorem cell22_909007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 8].length) (baseStart_909007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_909007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_909007 prefixEnd_909007 := by exact prefixLift 909007
  have htrace : WordTrace (prefixWord ++ tailWord_909007) baseStart_909007 baseEnd_909007 := by
    simpa [prefixWord, tailWord_909007, baseEnd_909007] using wordTrace_append hprefix tailTrace_909007
  have hstable : (prefixWord ++ tailWord_909007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909007).length < 2 ^ (prefixWord ++ tailWord_909007).sum := by decide
  have hdescent : baseEnd_909007 < baseStart_909007 := by decide
  rcases family_descends (prefixWord ++ tailWord_909007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909088 : List Nat := [2, 1, 1, 5, 1, 1, 4, 2, 2, 3]
def baseStart_909088 : Nat := 118140960795 + 909088 * 2 ^ 59
def prefixEnd_909088 : Nat := 4983230072969 + 3 ^ 40 * 909088 * 2
def baseEnd_909088 : Nat := 311199400823096281812791

theorem tailTrace_909088 : CollatzResearch.WordTrace tailWord_909088 prefixEnd_909088 311199400823096281812791 := by
  unfold tailWord_909088
  simp only [CollatzResearch.WordTrace]
  refine ⟨16578581665268455357319959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22104775553691273809759945 16578581665268455357319959)
  ·
    refine ⟨24867872497902683035979939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16578581665268455357319959 24867872497902683035979939)
    ·
      refine ⟨37301808746854024553969909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24867872497902683035979939 37301808746854024553969909)
      ·
        refine ⟨3497044570017564801934679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37301808746854024553969909 3497044570017564801934679)
        ·
          refine ⟨5245566855026347202902019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3497044570017564801934679 5245566855026347202902019)
          ·
            refine ⟨7868350282539520804353029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5245566855026347202902019 7868350282539520804353029)
            ·
              refine ⟨1475315677976160150816193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7868350282539520804353029 1475315677976160150816193)
              ·
                refine ⟨1106486758482120113112145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1475315677976160150816193 1106486758482120113112145)
                ·
                  refine ⟨829865068861590084834109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1106486758482120113112145 829865068861590084834109)
                  ·
                    refine ⟨311199400823096281812791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 829865068861590084834109 311199400823096281812791)
                    ·
                      rfl

theorem cell22_909088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 2, 2, 3].length) (baseStart_909088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_909088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_909088 prefixEnd_909088 := by exact prefixLift 909088
  have htrace : WordTrace (prefixWord ++ tailWord_909088) baseStart_909088 baseEnd_909088 := by
    simpa [prefixWord, tailWord_909088, baseEnd_909088] using wordTrace_append hprefix tailTrace_909088
  have hstable : (prefixWord ++ tailWord_909088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909088).length < 2 ^ (prefixWord ++ tailWord_909088).sum := by decide
  have hdescent : baseEnd_909088 < baseStart_909088 := by decide
  rcases family_descends (prefixWord ++ tailWord_909088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909116 : List Nat := [2, 2, 2, 2, 1, 1, 3, 1, 5, 3]
def baseStart_909116 : Nat := 118140960795 + 909116 * 2 ^ 59
def prefixEnd_909116 : Nat := 4983230072969 + 3 ^ 40 * 909116 * 2
def baseEnd_909116 : Nat := 311208985795313542112705

theorem tailTrace_909116 : CollatzResearch.WordTrace tailWord_909116 prefixEnd_909116 311208985795313542112705 := by
  unfold tailWord_909116
  simp only [CollatzResearch.WordTrace]
  refine ⟨16579092287217735748329601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22105456382956980997772801 16579092287217735748329601)
  ·
    refine ⟨12434319215413301811247201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16579092287217735748329601 12434319215413301811247201)
    ·
      refine ⟨9325739411559976358435401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12434319215413301811247201 9325739411559976358435401)
      ·
        refine ⟨6994304558669982268826551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9325739411559976358435401 6994304558669982268826551)
        ·
          refine ⟨10491456838004973403239827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6994304558669982268826551 10491456838004973403239827)
          ·
            refine ⟨15737185257007460104859741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10491456838004973403239827 15737185257007460104859741)
            ·
              refine ⟨5901444471377797539322403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15737185257007460104859741 5901444471377797539322403)
              ·
                refine ⟨8852166707066696308983605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5901444471377797539322403 8852166707066696308983605)
                ·
                  refine ⟨829890628787502778967213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8852166707066696308983605 829890628787502778967213)
                  ·
                    refine ⟨311208985795313542112705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 829890628787502778967213 311208985795313542112705)
                    ·
                      rfl

theorem cell22_909116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 5, 3].length) (baseStart_909116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_909116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_909116 prefixEnd_909116 := by exact prefixLift 909116
  have htrace : WordTrace (prefixWord ++ tailWord_909116) baseStart_909116 baseEnd_909116 := by
    simpa [prefixWord, tailWord_909116, baseEnd_909116] using wordTrace_append hprefix tailTrace_909116
  have hstable : (prefixWord ++ tailWord_909116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909116).length < 2 ^ (prefixWord ++ tailWord_909116).sum := by decide
  have hdescent : baseEnd_909116 < baseStart_909116 := by decide
  rcases family_descends (prefixWord ++ tailWord_909116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909118 : List Nat := [4, 2, 1, 2, 2, 2, 3, 6]
def baseStart_909118 : Nat := 118140960795 + 909118 * 2 ^ 59
def prefixEnd_909118 : Nat := 4983230072969 + 3 ^ 40 * 909118 * 2
def baseEnd_909118 : Nat := 34578852270687355951411

theorem tailTrace_909118 : CollatzResearch.WordTrace tailWord_909118 prefixEnd_909118 34578852270687355951411 := by
  unfold tailWord_909118
  simp only [CollatzResearch.WordTrace]
  refine ⟨4144782190053528229779001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22105505013618817225488005 4144782190053528229779001)
  ·
    refine ⟨3108586642540146172334251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4144782190053528229779001 3108586642540146172334251)
    ·
      refine ⟨4662879963810219258501377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3108586642540146172334251 4662879963810219258501377)
      ·
        refine ⟨3497159972857664443876033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4662879963810219258501377 3497159972857664443876033)
        ·
          refine ⟨2622869979643248332907025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3497159972857664443876033 2622869979643248332907025)
          ·
            refine ⟨1967152484732436249680269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2622869979643248332907025 1967152484732436249680269)
            ·
              refine ⟨737682181774663593630101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1967152484732436249680269 737682181774663593630101)
              ·
                refine ⟨34578852270687355951411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 737682181774663593630101 34578852270687355951411)
                ·
                  rfl

theorem cell22_909118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 6].length) (baseStart_909118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_909118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_909118 prefixEnd_909118 := by exact prefixLift 909118
  have htrace : WordTrace (prefixWord ++ tailWord_909118) baseStart_909118 baseEnd_909118 := by
    simpa [prefixWord, tailWord_909118, baseEnd_909118] using wordTrace_append hprefix tailTrace_909118
  have hstable : (prefixWord ++ tailWord_909118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909118).length < 2 ^ (prefixWord ++ tailWord_909118).sum := by decide
  have hdescent : baseEnd_909118 < baseStart_909118 := by decide
  rcases family_descends (prefixWord ++ tailWord_909118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909129 : List Nat := [1, 2, 1, 1, 2, 4, 2, 2, 7]
def baseStart_909129 : Nat := 118140960795 + 909129 * 2 ^ 59
def prefixEnd_909129 : Nat := 4983230072969 + 3 ^ 40 * 909129 * 2
def baseEnd_909129 : Nat := 103737811986995280512555

theorem tailTrace_909129 : CollatzResearch.WordTrace tailWord_909129 prefixEnd_909129 103737811986995280512555 := by
  unfold tailWord_909129
  simp only [CollatzResearch.WordTrace]
  refine ⟨33158658723388374716882441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22105772482258916477921627 33158658723388374716882441)
  ·
    refine ⟨24868994042541281037661831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33158658723388374716882441 24868994042541281037661831)
    ·
      refine ⟨37303491063811921556492747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24868994042541281037661831 37303491063811921556492747)
      ·
        refine ⟨55955236595717882334739121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37303491063811921556492747 55955236595717882334739121)
        ·
          refine ⟨41966427446788411751054341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55955236595717882334739121 41966427446788411751054341)
          ·
            refine ⟨7868705146272827203322689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41966427446788411751054341 7868705146272827203322689)
            ·
              refine ⟨5901528859704620402492017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7868705146272827203322689 5901528859704620402492017)
              ·
                refine ⟨4426146644778465301869013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5901528859704620402492017 4426146644778465301869013)
                ·
                  refine ⟨103737811986995280512555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4426146644778465301869013 103737811986995280512555)
                  ·
                    rfl

theorem cell22_909129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 7].length) (baseStart_909129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_909129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_909129 prefixEnd_909129 := by exact prefixLift 909129
  have htrace : WordTrace (prefixWord ++ tailWord_909129) baseStart_909129 baseEnd_909129 := by
    simpa [prefixWord, tailWord_909129, baseEnd_909129] using wordTrace_append hprefix tailTrace_909129
  have hstable : (prefixWord ++ tailWord_909129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909129).length < 2 ^ (prefixWord ++ tailWord_909129).sum := by decide
  have hdescent : baseEnd_909129 < baseStart_909129 := by decide
  rcases family_descends (prefixWord ++ tailWord_909129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909214 : List Nat := [4, 3, 1, 3, 1, 2, 2, 1, 5]
def baseStart_909214 : Nat := 118140960795 + 909214 * 2 ^ 59
def prefixEnd_909214 : Nat := 4983230072969 + 3 ^ 40 * 909214 * 2
def baseEnd_909214 : Nat := 103747511066024651054135

theorem tailTrace_909214 : CollatzResearch.WordTrace tailWord_909214 prefixEnd_909214 103747511066024651054135 := by
  unfold tailWord_909214
  simp only [CollatzResearch.WordTrace]
  refine ⟨4145219866010054279215837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22107839285386956155817797 4145219866010054279215837)
  ·
    refine ⟨1554457449753770354705939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4145219866010054279215837 1554457449753770354705939)
    ·
      refine ⟨2331686174630655532058909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1554457449753770354705939 2331686174630655532058909)
      ·
        refine ⟨874382315486495824522091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2331686174630655532058909 874382315486495824522091)
        ·
          refine ⟨1311573473229743736783137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 874382315486495824522091 1311573473229743736783137)
          ·
            refine ⟨983680104922307802587353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1311573473229743736783137 983680104922307802587353)
            ·
              refine ⟨737760078691730851940515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 983680104922307802587353 737760078691730851940515)
              ·
                refine ⟨1106640118037596277910773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 737760078691730851940515 1106640118037596277910773)
                ·
                  refine ⟨103747511066024651054135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1106640118037596277910773 103747511066024651054135)
                  ·
                    rfl

theorem cell22_909214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_909214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_909214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_909214 prefixEnd_909214 := by exact prefixLift 909214
  have htrace : WordTrace (prefixWord ++ tailWord_909214) baseStart_909214 baseEnd_909214 := by
    simpa [prefixWord, tailWord_909214, baseEnd_909214] using wordTrace_append hprefix tailTrace_909214
  have hstable : (prefixWord ++ tailWord_909214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909214).length < 2 ^ (prefixWord ++ tailWord_909214).sum := by decide
  have hdescent : baseEnd_909214 < baseStart_909214 := by decide
  rcases family_descends (prefixWord ++ tailWord_909214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909360 : List Nat := [2, 1, 1, 1, 2, 5, 3, 3, 4]
def baseStart_909360 : Nat := 118140960795 + 909360 * 2 ^ 59
def prefixEnd_909360 : Nat := 4983230072969 + 3 ^ 40 * 909360 * 2
def baseEnd_909360 : Nat := 103764170660592746337319

theorem tailTrace_909360 : CollatzResearch.WordTrace tailWord_909360 prefixEnd_909360 103764170660592746337319 := by
  unfold tailWord_909360
  simp only [CollatzResearch.WordTrace]
  refine ⟨16583541992775750584270767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22111389323701000779027689 16583541992775750584270767)
  ·
    refine ⟨24875312989163625876406151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16583541992775750584270767 24875312989163625876406151)
    ·
      refine ⟨37312969483745438814609227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24875312989163625876406151 37312969483745438814609227)
      ·
        refine ⟨55969454225618158221913841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37312969483745438814609227 55969454225618158221913841)
        ·
          refine ⟨41977090669213618666435381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55969454225618158221913841 41977090669213618666435381)
          ·
            refine ⟨3935352250238776749978317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41977090669213618666435381 3935352250238776749978317)
            ·
              refine ⟨1475757093839541281241869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3935352250238776749978317 1475757093839541281241869)
              ·
                refine ⟨553408910189827980465701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1475757093839541281241869 553408910189827980465701)
                ·
                  refine ⟨103764170660592746337319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 553408910189827980465701 103764170660592746337319)
                  ·
                    rfl

theorem cell22_909360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 3, 4].length) (baseStart_909360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_909360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_909360 prefixEnd_909360 := by exact prefixLift 909360
  have htrace : WordTrace (prefixWord ++ tailWord_909360) baseStart_909360 baseEnd_909360 := by
    simpa [prefixWord, tailWord_909360, baseEnd_909360] using wordTrace_append hprefix tailTrace_909360
  have hstable : (prefixWord ++ tailWord_909360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909360).length < 2 ^ (prefixWord ++ tailWord_909360).sum := by decide
  have hdescent : baseEnd_909360 < baseStart_909360 := by decide
  rcases family_descends (prefixWord ++ tailWord_909360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909405 : List Nat := [1, 4, 4, 1, 1, 1, 2, 8]
def baseStart_909405 : Nat := 118140960795 + 909405 * 2 ^ 59
def prefixEnd_909405 : Nat := 4983230072969 + 3 ^ 40 * 909405 * 2
def baseEnd_909405 : Nat := 34589768489045902404091

theorem tailTrace_909405 : CollatzResearch.WordTrace tailWord_909405 prefixEnd_909405 34589768489045902404091 := by
  unfold tailWord_909405
  simp only [CollatzResearch.WordTrace]
  refine ⟨33168725270388473853929669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22112483513592315902619779 33168725270388473853929669)
  ·
    refine ⟨6219135988197838847611813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33168725270388473853929669 6219135988197838847611813)
    ·
      refine ⟨1166087997787094783927215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6219135988197838847611813 1166087997787094783927215)
      ·
        refine ⟨1749131996680642175890823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1166087997787094783927215 1749131996680642175890823)
        ·
          refine ⟨2623697995020963263836235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1749131996680642175890823 2623697995020963263836235)
          ·
            refine ⟨3935546992531444895754353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2623697995020963263836235 3935546992531444895754353)
            ·
              refine ⟨2951660244398583671815765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3935546992531444895754353 2951660244398583671815765)
              ·
                refine ⟨34589768489045902404091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2951660244398583671815765 34589768489045902404091)
                ·
                  rfl

theorem cell22_909405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 8].length) (baseStart_909405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_909405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_909405 prefixEnd_909405 := by exact prefixLift 909405
  have htrace : WordTrace (prefixWord ++ tailWord_909405) baseStart_909405 baseEnd_909405 := by
    simpa [prefixWord, tailWord_909405, baseEnd_909405] using wordTrace_append hprefix tailTrace_909405
  have hstable : (prefixWord ++ tailWord_909405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909405).length < 2 ^ (prefixWord ++ tailWord_909405).sum := by decide
  have hdescent : baseEnd_909405 < baseStart_909405 := by decide
  rcases family_descends (prefixWord ++ tailWord_909405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909450 : List Nat := [3, 1, 2, 3, 1, 2, 2, 3, 5]
def baseStart_909450 : Nat := 118140960795 + 909450 * 2 ^ 59
def prefixEnd_909450 : Nat := 4983230072969 + 3 ^ 40 * 909450 * 2
def baseEnd_909450 : Nat := 103774440273682668087227

theorem tailTrace_909450 : CollatzResearch.WordTrace tailWord_909450 prefixEnd_909450 103774440273682668087227 := by
  unfold tailWord_909450
  simp only [CollatzResearch.WordTrace]
  refine ⟨8292591638806361634829451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22113577703483631026211869 8292591638806361634829451)
  ·
    refine ⟨12438887458209542452244177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8292591638806361634829451 12438887458209542452244177)
    ·
      refine ⟨9329165593657156839183133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12438887458209542452244177 9329165593657156839183133)
      ·
        refine ⟨3498437097621433814693675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9329165593657156839183133 3498437097621433814693675)
        ·
          refine ⟨5247655646432150722040513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3498437097621433814693675 5247655646432150722040513)
          ·
            refine ⟨3935741734824113041530385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5247655646432150722040513 3935741734824113041530385)
            ·
              refine ⟨2951806301118084781147789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3935741734824113041530385 2951806301118084781147789)
              ·
                refine ⟨1106927362919281792930421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2951806301118084781147789 1106927362919281792930421)
                ·
                  refine ⟨103774440273682668087227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1106927362919281792930421 103774440273682668087227)
                  ·
                    rfl

theorem cell22_909450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 3, 5].length) (baseStart_909450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_909450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_909450 prefixEnd_909450 := by exact prefixLift 909450
  have htrace : WordTrace (prefixWord ++ tailWord_909450) baseStart_909450 baseEnd_909450 := by
    simpa [prefixWord, tailWord_909450, baseEnd_909450] using wordTrace_append hprefix tailTrace_909450
  have hstable : (prefixWord ++ tailWord_909450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909450).length < 2 ^ (prefixWord ++ tailWord_909450).sum := by decide
  have hdescent : baseEnd_909450 < baseStart_909450 := by decide
  rcases family_descends (prefixWord ++ tailWord_909450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909495 : List Nat := [1, 1, 3, 1, 4, 3, 2, 1, 6]
def baseStart_909495 : Nat := 118140960795 + 909495 * 2 ^ 59
def prefixEnd_909495 : Nat := 4983230072969 + 3 ^ 40 * 909495 * 2
def baseEnd_909495 : Nat := 103779575080227628962181

theorem tailTrace_909495 : CollatzResearch.WordTrace tailWord_909495 prefixEnd_909495 103779575080227628962181 := by
  unfold tailWord_909495
  simp only [CollatzResearch.WordTrace]
  refine ⟨33172007840062419224705939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22114671893374946149803959 33172007840062419224705939)
  ·
    refine ⟨49758011760093628837058909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33172007840062419224705939 49758011760093628837058909)
    ·
      refine ⟨18659254410035110813897091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49758011760093628837058909 18659254410035110813897091)
      ·
        refine ⟨27988881615052666220845637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18659254410035110813897091 27988881615052666220845637)
        ·
          refine ⟨5247915302822374916408557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27988881615052666220845637 5247915302822374916408557)
          ·
            refine ⟨1967968238558390593653209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5247915302822374916408557 1967968238558390593653209)
            ·
              refine ⟨1475976178918792945239907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1967968238558390593653209 1475976178918792945239907)
              ·
                refine ⟨2213964268378189417859861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1475976178918792945239907 2213964268378189417859861)
                ·
                  refine ⟨103779575080227628962181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2213964268378189417859861 103779575080227628962181)
                  ·
                    rfl

theorem cell22_909495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 1, 6].length) (baseStart_909495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_909495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_909495 prefixEnd_909495 := by exact prefixLift 909495
  have htrace : WordTrace (prefixWord ++ tailWord_909495) baseStart_909495 baseEnd_909495 := by
    simpa [prefixWord, tailWord_909495, baseEnd_909495] using wordTrace_append hprefix tailTrace_909495
  have hstable : (prefixWord ++ tailWord_909495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909495).length < 2 ^ (prefixWord ++ tailWord_909495).sum := by decide
  have hdescent : baseEnd_909495 < baseStart_909495 := by decide
  rcases family_descends (prefixWord ++ tailWord_909495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909602 : List Nat := [3, 3, 1, 1, 3, 1, 1, 4, 5]
def baseStart_909602 : Nat := 118140960795 + 909602 * 2 ^ 59
def prefixEnd_909602 : Nat := 4983230072969 + 3 ^ 40 * 909602 * 2
def baseEnd_909602 : Nat := 103791784509123424820405

theorem tailTrace_909602 : CollatzResearch.WordTrace tailWord_909602 prefixEnd_909602 103791784509123424820405 := by
  unfold tailWord_909602
  simp only [CollatzResearch.WordTrace]
  refine ⟨8293977612668694124712765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22117273633783184332567373 8293977612668694124712765)
  ·
    refine ⟨3110241604750760296767287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8293977612668694124712765 3110241604750760296767287)
    ·
      refine ⟨4665362407126140445150931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3110241604750760296767287 4665362407126140445150931)
      ·
        refine ⟨6998043610689210667726397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4665362407126140445150931 6998043610689210667726397)
        ·
          refine ⟨2624266354008454000397399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6998043610689210667726397 2624266354008454000397399)
          ·
            refine ⟨3936399531012681000596099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2624266354008454000397399 3936399531012681000596099)
            ·
              refine ⟨5904599296519021500894149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3936399531012681000596099 5904599296519021500894149)
              ·
                refine ⟨1107112368097316531417653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5904599296519021500894149 1107112368097316531417653)
                ·
                  refine ⟨103791784509123424820405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1107112368097316531417653 103791784509123424820405)
                  ·
                    rfl

theorem cell22_909602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_909602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_909602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_909602 prefixEnd_909602 := by exact prefixLift 909602
  have htrace : WordTrace (prefixWord ++ tailWord_909602) baseStart_909602 baseEnd_909602 := by
    simpa [prefixWord, tailWord_909602, baseEnd_909602] using wordTrace_append hprefix tailTrace_909602
  have hstable : (prefixWord ++ tailWord_909602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909602).length < 2 ^ (prefixWord ++ tailWord_909602).sum := by decide
  have hdescent : baseEnd_909602 < baseStart_909602 := by decide
  rcases family_descends (prefixWord ++ tailWord_909602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909615 : List Nat := [1, 1, 2, 1, 2, 1, 5, 2, 3, 4]
def baseStart_909615 : Nat := 118140960795 + 909615 * 2 ^ 59
def prefixEnd_909615 : Nat := 4983230072969 + 3 ^ 40 * 909615 * 2
def baseEnd_909615 : Nat := 311379803693042573886175

theorem tailTrace_909615 : CollatzResearch.WordTrace tailWord_909615 prefixEnd_909615 311379803693042573886175 := by
  unfold tailWord_909615
  simp only [CollatzResearch.WordTrace]
  refine ⟨33176384599627679719074299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22117589733085119812716199 33176384599627679719074299)
  ·
    refine ⟨49764576899441519578611449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33176384599627679719074299 49764576899441519578611449)
    ·
      refine ⟨37323432674581139683958587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49764576899441519578611449 37323432674581139683958587)
      ·
        refine ⟨55985149011871709525937881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37323432674581139683958587 55985149011871709525937881)
        ·
          refine ⟨41988861758903782144453411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55985149011871709525937881 41988861758903782144453411)
          ·
            refine ⟨62983292638355673216680117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41988861758903782144453411 62983292638355673216680117)
            ·
              refine ⟨5904683684845844364063761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62983292638355673216680117 5904683684845844364063761)
              ·
                refine ⟨4428512763634383273047821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5904683684845844364063761 4428512763634383273047821)
                ·
                  refine ⟨1660692286362893727392933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4428512763634383273047821 1660692286362893727392933)
                  ·
                    refine ⟨311379803693042573886175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1660692286362893727392933 311379803693042573886175)
                    ·
                      rfl

theorem cell22_909615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 3, 4].length) (baseStart_909615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_909615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_909615 prefixEnd_909615 := by exact prefixLift 909615
  have htrace : WordTrace (prefixWord ++ tailWord_909615) baseStart_909615 baseEnd_909615 := by
    simpa [prefixWord, tailWord_909615, baseEnd_909615] using wordTrace_append hprefix tailTrace_909615
  have hstable : (prefixWord ++ tailWord_909615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909615).length < 2 ^ (prefixWord ++ tailWord_909615).sum := by decide
  have hdescent : baseEnd_909615 < baseStart_909615 := by decide
  rcases family_descends (prefixWord ++ tailWord_909615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909617 : List Nat := [1, 2, 2, 3, 4, 1, 1, 1, 2, 5]
def baseStart_909617 : Nat := 118140960795 + 909617 * 2 ^ 59
def prefixEnd_909617 : Nat := 4983230072969 + 3 ^ 40 * 909617 * 2
def baseEnd_909617 : Nat := 311380488333915235336169

theorem tailTrace_909617 : CollatzResearch.WordTrace tailWord_909617 prefixEnd_909617 311380488333915235336169 := by
  unfold tailWord_909617
  simp only [CollatzResearch.WordTrace]
  refine ⟨33176457545620434060647105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22117638363746956040431403 33176457545620434060647105)
  ·
    refine ⟨24882343159215325545485329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33176457545620434060647105 24882343159215325545485329)
    ·
      refine ⟨18661757369411494159113997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24882343159215325545485329 18661757369411494159113997)
      ·
        refine ⟨6998159013529310309667749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18661757369411494159113997 6998159013529310309667749)
        ·
          refine ⟨1312154815036745683062703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6998159013529310309667749 1312154815036745683062703)
          ·
            refine ⟨1968232222555118524594055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1312154815036745683062703 1968232222555118524594055)
            ·
              refine ⟨2952348333832677786891083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1968232222555118524594055 2952348333832677786891083)
              ·
                refine ⟨4428522500749016680336625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2952348333832677786891083 4428522500749016680336625)
                ·
                  refine ⟨3321391875561762510252469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4428522500749016680336625 3321391875561762510252469)
                  ·
                    refine ⟨311380488333915235336169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3321391875561762510252469 311380488333915235336169)
                    ·
                      rfl

theorem cell22_909617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 2, 5].length) (baseStart_909617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_909617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_909617 prefixEnd_909617 := by exact prefixLift 909617
  have htrace : WordTrace (prefixWord ++ tailWord_909617) baseStart_909617 baseEnd_909617 := by
    simpa [prefixWord, tailWord_909617, baseEnd_909617] using wordTrace_append hprefix tailTrace_909617
  have hstable : (prefixWord ++ tailWord_909617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909617).length < 2 ^ (prefixWord ++ tailWord_909617).sum := by decide
  have hdescent : baseEnd_909617 < baseStart_909617 := by decide
  rcases family_descends (prefixWord ++ tailWord_909617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909649 : List Nat := [1, 2, 2, 1, 4, 2, 4, 1, 1, 4]
def baseStart_909649 : Nat := 118140960795 + 909649 * 2 ^ 59
def prefixEnd_909649 : Nat := 4983230072969 + 3 ^ 40 * 909649 * 2
def baseEnd_909649 : Nat := 311391442587877818536071

theorem tailTrace_909649 : CollatzResearch.WordTrace tailWord_909649 prefixEnd_909649 311391442587877818536071 := by
  unfold tailWord_909649
  simp only [CollatzResearch.WordTrace]
  refine ⟨33177624681504503525812001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22118416454336335683874667 33177624681504503525812001)
  ·
    refine ⟨24883218511128377644359001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33177624681504503525812001 24883218511128377644359001)
    ·
      refine ⟨18662413883346283233269251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24883218511128377644359001 18662413883346283233269251)
      ·
        refine ⟨27993620825019424849903877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18662413883346283233269251 27993620825019424849903877)
        ·
          refine ⟨5248803904691142159356977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27993620825019424849903877 5248803904691142159356977)
          ·
            refine ⟨3936602928518356619517733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5248803904691142159356977 3936602928518356619517733)
            ·
              refine ⟨738113049097191866159575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3936602928518356619517733 738113049097191866159575)
              ·
                refine ⟨1107169573645787799239363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 738113049097191866159575 1107169573645787799239363)
                ·
                  refine ⟨1660754360468681698859045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1107169573645787799239363 1660754360468681698859045)
                  ·
                    refine ⟨311391442587877818536071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1660754360468681698859045 311391442587877818536071)
                    ·
                      rfl

theorem cell22_909649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 1, 1, 4].length) (baseStart_909649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_909649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_909649 prefixEnd_909649 := by exact prefixLift 909649
  have htrace : WordTrace (prefixWord ++ tailWord_909649) baseStart_909649 baseEnd_909649 := by
    simpa [prefixWord, tailWord_909649, baseEnd_909649] using wordTrace_append hprefix tailTrace_909649
  have hstable : (prefixWord ++ tailWord_909649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909649).length < 2 ^ (prefixWord ++ tailWord_909649).sum := by decide
  have hdescent : baseEnd_909649 < baseStart_909649 := by decide
  rcases family_descends (prefixWord ++ tailWord_909649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909814 : List Nat := [5, 1, 1, 1, 2, 1, 1, 4, 1, 5]
def baseStart_909814 : Nat := 118140960795 + 909814 * 2 ^ 59
def prefixEnd_909814 : Nat := 4983230072969 + 3 ^ 40 * 909814 * 2
def baseEnd_909814 : Nat := 311447925459872388160565

theorem tailTrace_909814 : CollatzResearch.WordTrace tailWord_909814 prefixEnd_909814 311447925459872388160565 := by
  unfold tailWord_909814
  simp only [CollatzResearch.WordTrace]
  refine ⟨2073977670369171044098031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22122428483937824470378997 2073977670369171044098031)
  ·
    refine ⟨3110966505553756566147047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2073977670369171044098031 3110966505553756566147047)
    ·
      refine ⟨4666449758330634849220571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3110966505553756566147047 4666449758330634849220571)
      ·
        refine ⟨6999674637495952273830857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4666449758330634849220571 6999674637495952273830857)
        ·
          refine ⟨5249755978121964205373143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6999674637495952273830857 5249755978121964205373143)
          ·
            refine ⟨7874633967182946308059715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5249755978121964205373143 7874633967182946308059715)
            ·
              refine ⟨11811950950774419462089573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7874633967182946308059715 11811950950774419462089573)
              ·
                refine ⟨2214740803270203649141795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11811950950774419462089573 2214740803270203649141795)
                ·
                  refine ⟨3322111204905305473712693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2214740803270203649141795 3322111204905305473712693)
                  ·
                    refine ⟨311447925459872388160565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3322111204905305473712693 311447925459872388160565)
                    ·
                      rfl

theorem cell22_909814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_909814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_909814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_909814 prefixEnd_909814 := by exact prefixLift 909814
  have htrace : WordTrace (prefixWord ++ tailWord_909814) baseStart_909814 baseEnd_909814 := by
    simpa [prefixWord, tailWord_909814, baseEnd_909814] using wordTrace_append hprefix tailTrace_909814
  have hstable : (prefixWord ++ tailWord_909814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909814).length < 2 ^ (prefixWord ++ tailWord_909814).sum := by decide
  have hdescent : baseEnd_909814 < baseStart_909814 := by decide
  rcases family_descends (prefixWord ++ tailWord_909814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909831 : List Nat := [1, 1, 4, 3, 3, 1, 1, 1, 4, 3]
def baseStart_909831 : Nat := 118140960795 + 909831 * 2 ^ 59
def prefixEnd_909831 : Nat := 4983230072969 + 3 ^ 40 * 909831 * 2
def baseEnd_909831 : Nat := 311453744907290010485513

theorem tailTrace_909831 : CollatzResearch.WordTrace tailWord_909831 prefixEnd_909831 311453744907290010485513 := by
  unfold tailWord_909831
  simp only [CollatzResearch.WordTrace]
  refine ⟨33184262766845148608937347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22122841844563432405958231 33184262766845148608937347)
  ·
    refine ⟨49776394150267722913406021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33184262766845148608937347 49776394150267722913406021)
    ·
      refine ⟨9333073903175198046263629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49776394150267722913406021 9333073903175198046263629)
      ·
        refine ⟨3499902713690699267348861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9333073903175198046263629 3499902713690699267348861)
        ·
          refine ⟨1312463517634012225255823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3499902713690699267348861 1312463517634012225255823)
          ·
            refine ⟨1968695276451018337883735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1312463517634012225255823 1968695276451018337883735)
            ·
              refine ⟨2953042914676527506825603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1968695276451018337883735 2953042914676527506825603)
              ·
                refine ⟨4429564372014791260238405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2953042914676527506825603 4429564372014791260238405)
                ·
                  refine ⟨830543319752773361294701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4429564372014791260238405 830543319752773361294701)
                  ·
                    refine ⟨311453744907290010485513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 830543319752773361294701 311453744907290010485513)
                    ·
                      rfl

theorem cell22_909831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 4, 3].length) (baseStart_909831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_909831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_909831 prefixEnd_909831 := by exact prefixLift 909831
  have htrace : WordTrace (prefixWord ++ tailWord_909831) baseStart_909831 baseEnd_909831 := by
    simpa [prefixWord, tailWord_909831, baseEnd_909831] using wordTrace_append hprefix tailTrace_909831
  have hstable : (prefixWord ++ tailWord_909831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909831).length < 2 ^ (prefixWord ++ tailWord_909831).sum := by decide
  have hdescent : baseEnd_909831 < baseStart_909831 := by decide
  rcases family_descends (prefixWord ++ tailWord_909831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909848 : List Nat := [2, 1, 2, 3, 3, 2, 3, 1, 2, 3]
def baseStart_909848 : Nat := 118140960795 + 909848 * 2 ^ 59
def prefixEnd_909848 : Nat := 4983230072969 + 3 ^ 40 * 909848 * 2
def baseEnd_909848 : Nat := 311459564354707632810461

theorem tailTrace_909848 : CollatzResearch.WordTrace tailWord_909848 prefixEnd_909848 311459564354707632810461 := by
  unfold tailWord_909848
  simp only [CollatzResearch.WordTrace]
  refine ⟨16592441403891780256153099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22123255205189040341537465 16592441403891780256153099)
  ·
    refine ⟨24888662105837670384229649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16592441403891780256153099 24888662105837670384229649)
    ·
      refine ⟨18666496579378252788172237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24888662105837670384229649 18666496579378252788172237)
      ·
        refine ⟨6999936217266844795564589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18666496579378252788172237 6999936217266844795564589)
        ·
          refine ⟨2624976081475066798336721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6999936217266844795564589 2624976081475066798336721)
          ·
            refine ⟨1968732061106300098752541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2624976081475066798336721 1968732061106300098752541)
            ·
              refine ⟨738274522914862537032203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1968732061106300098752541 738274522914862537032203)
              ·
                refine ⟨1107411784372293805548305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 738274522914862537032203 1107411784372293805548305)
                ·
                  refine ⟨830558838279220354161229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1107411784372293805548305 830558838279220354161229)
                  ·
                    refine ⟨311459564354707632810461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 830558838279220354161229 311459564354707632810461)
                    ·
                      rfl

theorem cell22_909848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 1, 2, 3].length) (baseStart_909848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_909848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_909848 prefixEnd_909848 := by exact prefixLift 909848
  have htrace : WordTrace (prefixWord ++ tailWord_909848) baseStart_909848 baseEnd_909848 := by
    simpa [prefixWord, tailWord_909848, baseEnd_909848] using wordTrace_append hprefix tailTrace_909848
  have hstable : (prefixWord ++ tailWord_909848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909848).length < 2 ^ (prefixWord ++ tailWord_909848).sum := by decide
  have hdescent : baseEnd_909848 < baseStart_909848 := by decide
  rcases family_descends (prefixWord ++ tailWord_909848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909872 : List Nat := [2, 1, 1, 1, 2, 3, 3, 2, 7]
def baseStart_909872 : Nat := 118140960795 + 909872 * 2 ^ 59
def prefixEnd_909872 : Nat := 4983230072969 + 3 ^ 40 * 909872 * 2
def baseEnd_909872 : Nat := 103822593348393190070129

theorem tailTrace_909872 : CollatzResearch.WordTrace tailWord_909872 prefixEnd_909872 103822593348393190070129 := by
  unfold tailWord_909872
  simp only [CollatzResearch.WordTrace]
  refine ⟨16592879079848306305589935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22123838773131075074119913 16592879079848306305589935)
  ·
    refine ⟨24889318619772459458384903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16592879079848306305589935 24889318619772459458384903)
    ·
      refine ⟨37333977929658689187577355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24889318619772459458384903 37333977929658689187577355)
      ·
        refine ⟨56000966894488033781366033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37333977929658689187577355 56000966894488033781366033)
        ·
          refine ⟨42000725170866025336024525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56000966894488033781366033 42000725170866025336024525)
          ·
            refine ⟨15750271939074759501009197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42000725170866025336024525 15750271939074759501009197)
            ·
              refine ⟨5906351977153034812878449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15750271939074759501009197 5906351977153034812878449)
              ·
                refine ⟨4429763982864776109658837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5906351977153034812878449 4429763982864776109658837)
                ·
                  refine ⟨103822593348393190070129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4429763982864776109658837 103822593348393190070129)
                  ·
                    rfl

theorem cell22_909872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 7].length) (baseStart_909872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_909872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_909872 prefixEnd_909872 := by exact prefixLift 909872
  have htrace : WordTrace (prefixWord ++ tailWord_909872) baseStart_909872 baseEnd_909872 := by
    simpa [prefixWord, tailWord_909872, baseEnd_909872] using wordTrace_append hprefix tailTrace_909872
  have hstable : (prefixWord ++ tailWord_909872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909872).length < 2 ^ (prefixWord ++ tailWord_909872).sum := by decide
  have hdescent : baseEnd_909872 < baseStart_909872 := by decide
  rcases family_descends (prefixWord ++ tailWord_909872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909889 : List Nat := [1, 2, 5, 1, 1, 2, 2, 1, 7]
def baseStart_909889 : Nat := 118140960795 + 909889 * 2 ^ 59
def prefixEnd_909889 : Nat := 4983230072969 + 3 ^ 40 * 909889 * 2
def baseEnd_909889 : Nat := 103824533164199064178445

theorem tailTrace_909889 : CollatzResearch.WordTrace tailWord_909889 prefixEnd_909889 103824533164199064178445 := by
  unfold tailWord_909889
  simp only [CollatzResearch.WordTrace]
  refine ⟨33186378200635024514548721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22124252133756683009699147 33186378200635024514548721)
  ·
    refine ⟨24889783650476268385911541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33186378200635024514548721 24889783650476268385911541)
    ·
      refine ⟨2333417217232150161179207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24889783650476268385911541 2333417217232150161179207)
      ·
        refine ⟨3500125825848225241768811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2333417217232150161179207 3500125825848225241768811)
        ·
          refine ⟨5250188738772337862653217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3500125825848225241768811 5250188738772337862653217)
          ·
            refine ⟨3937641554079253396989913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5250188738772337862653217 3937641554079253396989913)
            ·
              refine ⟨2953231165559440047742435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3937641554079253396989913 2953231165559440047742435)
              ·
                refine ⟨4429846748339160071613653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2953231165559440047742435 4429846748339160071613653)
                ·
                  refine ⟨103824533164199064178445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4429846748339160071613653 103824533164199064178445)
                  ·
                    rfl

theorem cell22_909889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 7].length) (baseStart_909889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_909889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_909889 prefixEnd_909889 := by exact prefixLift 909889
  have htrace : WordTrace (prefixWord ++ tailWord_909889) baseStart_909889 baseEnd_909889 := by
    simpa [prefixWord, tailWord_909889, baseEnd_909889] using wordTrace_append hprefix tailTrace_909889
  have hstable : (prefixWord ++ tailWord_909889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909889).length < 2 ^ (prefixWord ++ tailWord_909889).sum := by decide
  have hdescent : baseEnd_909889 < baseStart_909889 := by decide
  rcases family_descends (prefixWord ++ tailWord_909889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909966 : List Nat := [4, 1, 1, 3, 1, 1, 4, 1, 1, 5]
def baseStart_909966 : Nat := 118140960795 + 909966 * 2 ^ 59
def prefixEnd_909966 : Nat := 4983230072969 + 3 ^ 40 * 909966 * 2
def baseEnd_909966 : Nat := 311499958166194658360099

theorem tailTrace_909966 : CollatzResearch.WordTrace tailWord_909966 prefixEnd_909966 311499958166194658360099 := by
  unfold tailWord_909966
  simp only [CollatzResearch.WordTrace]
  refine ⟨4148648327669508333137719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22126124414237377776734501 4148648327669508333137719)
  ·
    refine ⟨6222972491504262499706579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4148648327669508333137719 6222972491504262499706579)
    ·
      refine ⟨9334458737256393749559869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6222972491504262499706579 9334458737256393749559869)
      ·
        refine ⟨3500422026471147656084951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9334458737256393749559869 3500422026471147656084951)
        ·
          refine ⟨5250633039706721484127427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3500422026471147656084951 5250633039706721484127427)
          ·
            refine ⟨7875949559560082226191141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5250633039706721484127427 7875949559560082226191141)
            ·
              refine ⟨1476740542417515417410839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7875949559560082226191141 1476740542417515417410839)
              ·
                refine ⟨2215110813626273126116259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1476740542417515417410839 2215110813626273126116259)
                ·
                  refine ⟨3322666220439409689174389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2215110813626273126116259 3322666220439409689174389)
                  ·
                    refine ⟨311499958166194658360099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3322666220439409689174389 311499958166194658360099)
                    ·
                      rfl

theorem cell22_909966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 1, 1, 5].length) (baseStart_909966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_909966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_909966 prefixEnd_909966 := by exact prefixLift 909966
  have htrace : WordTrace (prefixWord ++ tailWord_909966) baseStart_909966 baseEnd_909966 := by
    simpa [prefixWord, tailWord_909966, baseEnd_909966] using wordTrace_append hprefix tailTrace_909966
  have hstable : (prefixWord ++ tailWord_909966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909966).length < 2 ^ (prefixWord ++ tailWord_909966).sum := by decide
  have hdescent : baseEnd_909966 < baseStart_909966 := by decide
  rcases family_descends (prefixWord ++ tailWord_909966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909981 : List Nat := [1, 4, 2, 1, 1, 1, 5, 1, 2, 4]
def baseStart_909981 : Nat := 118140960795 + 909981 * 2 ^ 59
def prefixEnd_909981 : Nat := 4983230072969 + 3 ^ 40 * 909981 * 2
def baseEnd_909981 : Nat := 311505092972739619235053

theorem tailTrace_909981 : CollatzResearch.WordTrace tailWord_909981 prefixEnd_909981 311505092972739619235053 := by
  unfold tailWord_909981
  simp only [CollatzResearch.WordTrace]
  refine ⟨33189733716301724226897797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22126489144201149484598531 33189733716301724226897797)
  ·
    refine ⟨6223075071806573292543337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33189733716301724226897797 6223075071806573292543337)
    ·
      refine ⟨4667306303854929969407503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6223075071806573292543337 4667306303854929969407503)
      ·
        refine ⟨7000959455782394954111255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4667306303854929969407503 7000959455782394954111255)
        ·
          refine ⟨10501439183673592431166883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7000959455782394954111255 10501439183673592431166883)
          ·
            refine ⟨15752158775510388646750325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10501439183673592431166883 15752158775510388646750325)
            ·
              refine ⟨1476764885204098935632843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15752158775510388646750325 1476764885204098935632843)
              ·
                refine ⟨2215147327806148403449265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1476764885204098935632843 2215147327806148403449265)
                ·
                  refine ⟨1661360495854611302586949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2215147327806148403449265 1661360495854611302586949)
                  ·
                    refine ⟨311505092972739619235053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1661360495854611302586949 311505092972739619235053)
                    ·
                      rfl

theorem cell22_909981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_909981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_909981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_909981 prefixEnd_909981 := by exact prefixLift 909981
  have htrace : WordTrace (prefixWord ++ tailWord_909981) baseStart_909981 baseEnd_909981 := by
    simpa [prefixWord, tailWord_909981, baseEnd_909981] using wordTrace_append hprefix tailTrace_909981
  have hstable : (prefixWord ++ tailWord_909981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909981).length < 2 ^ (prefixWord ++ tailWord_909981).sum := by decide
  have hdescent : baseEnd_909981 < baseStart_909981 := by decide
  rcases family_descends (prefixWord ++ tailWord_909981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910017 : List Nat := [1, 2, 6, 2, 2, 1, 1, 1, 1, 5]
def baseStart_910017 : Nat := 118140960795 + 910017 * 2 ^ 59
def prefixEnd_910017 : Nat := 4983230072969 + 3 ^ 40 * 910017 * 2
def baseEnd_910017 : Nat := 311517416508447525334943

theorem tailTrace_910017 : CollatzResearch.WordTrace tailWord_910017 prefixEnd_910017 311517416508447525334943 := by
  unfold tailWord_910017
  simp only [CollatzResearch.WordTrace]
  refine ⟨33191046744171302375208305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22127364496114201583472203 33191046744171302375208305)
  ·
    refine ⟨24893285058128476781406229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33191046744171302375208305 24893285058128476781406229)
    ·
      refine ⟨1166872737099772349128417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24893285058128476781406229 1166872737099772349128417)
      ·
        refine ⟨875154552824829261846313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1166872737099772349128417 875154552824829261846313)
        ·
          refine ⟨656365914618621946384735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 875154552824829261846313 656365914618621946384735)
          ·
            refine ⟨984548871927932919577103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 656365914618621946384735 984548871927932919577103)
            ·
              refine ⟨1476823307891899379365655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 984548871927932919577103 1476823307891899379365655)
              ·
                refine ⟨2215234961837849069048483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1476823307891899379365655 2215234961837849069048483)
                ·
                  refine ⟨3322852442756773603572725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2215234961837849069048483 3322852442756773603572725)
                  ·
                    refine ⟨311517416508447525334943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3322852442756773603572725 311517416508447525334943)
                    ·
                      rfl

theorem cell22_910017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_910017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_910017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_910017 prefixEnd_910017 := by exact prefixLift 910017
  have htrace : WordTrace (prefixWord ++ tailWord_910017) baseStart_910017 baseEnd_910017 := by
    simpa [prefixWord, tailWord_910017, baseEnd_910017] using wordTrace_append hprefix tailTrace_910017
  have hstable : (prefixWord ++ tailWord_910017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910017).length < 2 ^ (prefixWord ++ tailWord_910017).sum := by decide
  have hdescent : baseEnd_910017 < baseStart_910017 := by decide
  rcases family_descends (prefixWord ++ tailWord_910017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910028 : List Nat := [2, 2, 1, 5, 1, 1, 2, 2, 3, 3]
def baseStart_910028 : Nat := 118140960795 + 910028 * 2 ^ 59
def prefixEnd_910028 : Nat := 4983230072969 + 3 ^ 40 * 910028 * 2
def baseEnd_910028 : Nat := 311521182033247163309909

theorem tailTrace_910028 : CollatzResearch.WordTrace tailWord_910028 prefixEnd_910028 311521182033247163309909 := by
  unfold tailWord_910028
  simp only [CollatzResearch.WordTrace]
  refine ⟨16595723973565725626929369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22127631964754300835905825 16595723973565725626929369)
  ·
    refine ⟨12446792980174294220197027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16595723973565725626929369 12446792980174294220197027)
    ·
      refine ⟨18670189470261441330295541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12446792980174294220197027 18670189470261441330295541)
      ·
        refine ⟨1750330262837010124715207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18670189470261441330295541 1750330262837010124715207)
        ·
          refine ⟨2625495394255515187072811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1750330262837010124715207 2625495394255515187072811)
          ·
            refine ⟨3938243091383272780609217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2625495394255515187072811 3938243091383272780609217)
            ·
              refine ⟨2953682318537454585456913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3938243091383272780609217 2953682318537454585456913)
              ·
                refine ⟨2215261738903090939092685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2953682318537454585456913 2215261738903090939092685)
                ·
                  refine ⟨830723152088659102159757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2215261738903090939092685 830723152088659102159757)
                  ·
                    refine ⟨311521182033247163309909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 830723152088659102159757 311521182033247163309909)
                    ·
                      rfl

theorem cell22_910028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 2, 3, 3].length) (baseStart_910028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_910028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_910028 prefixEnd_910028 := by exact prefixLift 910028
  have htrace : WordTrace (prefixWord ++ tailWord_910028) baseStart_910028 baseEnd_910028 := by
    simpa [prefixWord, tailWord_910028, baseEnd_910028] using wordTrace_append hprefix tailTrace_910028
  have hstable : (prefixWord ++ tailWord_910028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910028).length < 2 ^ (prefixWord ++ tailWord_910028).sum := by decide
  have hdescent : baseEnd_910028 < baseStart_910028 := by decide
  rcases family_descends (prefixWord ++ tailWord_910028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910062 : List Nat := [4, 1, 2, 1, 1, 4, 3, 2, 1, 3]
def baseStart_910062 : Nat := 118140960795 + 910062 * 2 ^ 59
def prefixEnd_910062 : Nat := 4983230072969 + 3 ^ 40 * 910062 * 2
def baseEnd_910062 : Nat := 311532820928082407959805

theorem tailTrace_910062 : CollatzResearch.WordTrace tailWord_910062 prefixEnd_910062 311532820928082407959805 := by
  unfold tailWord_910062
  simp only [CollatzResearch.WordTrace]
  refine ⟨4149086003626034382574555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22128458686005516707064293 4149086003626034382574555)
  ·
    refine ⟨6223629005439051573861833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4149086003626034382574555 6223629005439051573861833)
    ·
      refine ⟨4667721754079288680396375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6223629005439051573861833 4667721754079288680396375)
      ·
        refine ⟨7001582631118933020594563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4667721754079288680396375 7001582631118933020594563)
        ·
          refine ⟨10502373946678399530891845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7001582631118933020594563 10502373946678399530891845)
          ·
            refine ⟨1969195115002199912042221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10502373946678399530891845 1969195115002199912042221)
            ·
              refine ⟨738448168125824967015833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1969195115002199912042221 738448168125824967015833)
              ·
                refine ⟨553836126094368725261875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 738448168125824967015833 553836126094368725261875)
                ·
                  refine ⟨830754189141553087892813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 553836126094368725261875 830754189141553087892813)
                  ·
                    refine ⟨311532820928082407959805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 830754189141553087892813 311532820928082407959805)
                    ·
                      rfl

theorem cell22_910062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 2, 1, 3].length) (baseStart_910062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_910062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_910062 prefixEnd_910062 := by exact prefixLift 910062
  have htrace : WordTrace (prefixWord ++ tailWord_910062) baseStart_910062 baseEnd_910062 := by
    simpa [prefixWord, tailWord_910062, baseEnd_910062] using wordTrace_append hprefix tailTrace_910062
  have hstable : (prefixWord ++ tailWord_910062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910062).length < 2 ^ (prefixWord ++ tailWord_910062).sum := by decide
  have hdescent : baseEnd_910062 < baseStart_910062 := by decide
  rcases family_descends (prefixWord ++ tailWord_910062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910088 : List Nat := [2, 1, 3, 2, 2, 2, 3, 2, 1, 4]
def baseStart_910088 : Nat := 118140960795 + 910088 * 2 ^ 59
def prefixEnd_910088 : Nat := 4983230072969 + 3 ^ 40 * 910088 * 2
def baseEnd_910088 : Nat := 311541721259427006809725

theorem tailTrace_910088 : CollatzResearch.WordTrace tailWord_910088 prefixEnd_910088 311541721259427006809725 := by
  unfold tailWord_910088
  simp only [CollatzResearch.WordTrace]
  refine ⟨16596818163457040750521459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22129090884609387667361945 16596818163457040750521459)
  ·
    refine ⟨24895227245185561125782189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16596818163457040750521459 24895227245185561125782189)
    ·
      refine ⟨9335710216944585422168321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24895227245185561125782189 9335710216944585422168321)
      ·
        refine ⟨7001782662708439066626241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9335710216944585422168321 7001782662708439066626241)
        ·
          refine ⟨5251336997031329299969681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7001782662708439066626241 5251336997031329299969681)
          ·
            refine ⟨3938502747773496974977261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5251336997031329299969681 3938502747773496974977261)
            ·
              refine ⟨1476938530415061365616473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3938502747773496974977261 1476938530415061365616473)
              ·
                refine ⟨1107703897811296024212355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1476938530415061365616473 1107703897811296024212355)
                ·
                  refine ⟨1661555846716944036318533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1107703897811296024212355 1661555846716944036318533)
                  ·
                    refine ⟨311541721259427006809725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1661555846716944036318533 311541721259427006809725)
                    ·
                      rfl

theorem cell22_910088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 2, 1, 4].length) (baseStart_910088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_910088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_910088 prefixEnd_910088 := by exact prefixLift 910088
  have htrace : WordTrace (prefixWord ++ tailWord_910088) baseStart_910088 baseEnd_910088 := by
    simpa [prefixWord, tailWord_910088, baseEnd_910088] using wordTrace_append hprefix tailTrace_910088
  have hstable : (prefixWord ++ tailWord_910088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910088).length < 2 ^ (prefixWord ++ tailWord_910088).sum := by decide
  have hdescent : baseEnd_910088 < baseStart_910088 := by decide
  rcases family_descends (prefixWord ++ tailWord_910088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910101 : List Nat := [1, 3, 2, 1, 2, 2, 3, 2, 1, 5]
def baseStart_910101 : Nat := 118140960795 + 910101 * 2 ^ 59
def prefixEnd_910101 : Nat := 4983230072969 + 3 ^ 40 * 910101 * 2
def baseEnd_910101 : Nat := 311546171425099306234685

theorem tailTrace_910101 : CollatzResearch.WordTrace tailWord_910101 prefixEnd_910101 311546171425099306234685 := by
  unfold tailWord_910101
  simp only [CollatzResearch.WordTrace]
  refine ⟨33194110475866984721266157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22129406983911323147510771 33194110475866984721266157)
  ·
    refine ⟨12447791428450119270474809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33194110475866984721266157 12447791428450119270474809)
    ·
      refine ⟨9335843571337589452856107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12447791428450119270474809 9335843571337589452856107)
      ·
        refine ⟨14003765357006384179284161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9335843571337589452856107 14003765357006384179284161)
        ·
          refine ⟨10502824017754788134463121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14003765357006384179284161 10502824017754788134463121)
          ·
            refine ⟨7877118013316091100847341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10502824017754788134463121 7877118013316091100847341)
            ·
              refine ⟨2953919254993534162817753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7877118013316091100847341 2953919254993534162817753)
              ·
                refine ⟨2215439441245150622113315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2953919254993534162817753 2215439441245150622113315)
                ·
                  refine ⟨3323159161867725933169973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2215439441245150622113315 3323159161867725933169973)
                  ·
                    refine ⟨311546171425099306234685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3323159161867725933169973 311546171425099306234685)
                    ·
                      rfl

theorem cell22_910101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_910101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_910101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_910101 prefixEnd_910101 := by exact prefixLift 910101
  have htrace : WordTrace (prefixWord ++ tailWord_910101) baseStart_910101 baseEnd_910101 := by
    simpa [prefixWord, tailWord_910101, baseEnd_910101] using wordTrace_append hprefix tailTrace_910101
  have hstable : (prefixWord ++ tailWord_910101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910101).length < 2 ^ (prefixWord ++ tailWord_910101).sum := by decide
  have hdescent : baseEnd_910101 < baseStart_910101 := by decide
  rcases family_descends (prefixWord ++ tailWord_910101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910131 : List Nat := [1, 1, 1, 2, 6, 1, 3, 7]
def baseStart_910131 : Nat := 118140960795 + 910131 * 2 ^ 59
def prefixEnd_910131 : Nat := 4983230072969 + 3 ^ 40 * 910131 * 2
def baseEnd_910131 : Nat := 34617382337576580887177

theorem tailTrace_910131 : CollatzResearch.WordTrace tailWord_910131 prefixEnd_910131 34617382337576580887177 := by
  unfold tailWord_910131
  simp only [CollatzResearch.WordTrace]
  refine ⟨33195204665758299844858247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22130136443838866563238831 33195204665758299844858247)
  ·
    refine ⟨49792806998637449767287371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33195204665758299844858247 49792806998637449767287371)
    ·
      refine ⟨74689210497956174650931057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49792806998637449767287371 74689210497956174650931057)
      ·
        refine ⟨56016907873467130988198293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74689210497956174650931057 56016907873467130988198293)
        ·
          refine ⟨2625792556568771765071795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 56016907873467130988198293 2625792556568771765071795)
          ·
            refine ⟨3938688834853157647607693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2625792556568771765071795 3938688834853157647607693)
            ·
              refine ⟨1477008313069934117852885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3938688834853157647607693 1477008313069934117852885)
              ·
                refine ⟨34617382337576580887177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1477008313069934117852885 34617382337576580887177)
                ·
                  rfl

theorem cell22_910131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 7].length) (baseStart_910131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_910131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_910131 prefixEnd_910131 := by exact prefixLift 910131
  have htrace : WordTrace (prefixWord ++ tailWord_910131) baseStart_910131 baseEnd_910131 := by
    simpa [prefixWord, tailWord_910131, baseEnd_910131] using wordTrace_append hprefix tailTrace_910131
  have hstable : (prefixWord ++ tailWord_910131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910131).length < 2 ^ (prefixWord ++ tailWord_910131).sum := by decide
  have hdescent : baseEnd_910131 < baseStart_910131 := by decide
  rcases family_descends (prefixWord ++ tailWord_910131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910176 : List Nat := [2, 1, 1, 3, 3, 1, 3, 1, 7]
def baseStart_910176 : Nat := 118140960795 + 910176 * 2 ^ 59
def prefixEnd_910176 : Nat := 4983230072969 + 3 ^ 40 * 910176 * 2
def baseEnd_910176 : Nat := 103857281819274703536485

theorem tailTrace_910176 : CollatzResearch.WordTrace tailWord_910176 prefixEnd_910176 103857281819274703536485 := by
  unfold tailWord_910176
  simp only [CollatzResearch.WordTrace]
  refine ⟨16598422975297636265123191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22131230633730181686830921 16598422975297636265123191)
  ·
    refine ⟨24897634462946454397684787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16598422975297636265123191 24897634462946454397684787)
    ·
      refine ⟨37346451694419681596527181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24897634462946454397684787 37346451694419681596527181)
      ·
        refine ⟨14004919385407380598697693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37346451694419681596527181 14004919385407380598697693)
        ·
          refine ⟨5251844769527767724511635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14004919385407380598697693 5251844769527767724511635)
          ·
            refine ⟨7877767154291651586767453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5251844769527767724511635 7877767154291651586767453)
            ·
              refine ⟨2954162682859369345037795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7877767154291651586767453 2954162682859369345037795)
              ·
                refine ⟨4431244024289054017556693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2954162682859369345037795 4431244024289054017556693)
                ·
                  refine ⟨103857281819274703536485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4431244024289054017556693 103857281819274703536485)
                  ·
                    rfl

theorem cell22_910176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 7].length) (baseStart_910176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_910176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_910176 prefixEnd_910176 := by exact prefixLift 910176
  have htrace : WordTrace (prefixWord ++ tailWord_910176) baseStart_910176 baseEnd_910176 := by
    simpa [prefixWord, tailWord_910176, baseEnd_910176] using wordTrace_append hprefix tailTrace_910176
  have hstable : (prefixWord ++ tailWord_910176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910176).length < 2 ^ (prefixWord ++ tailWord_910176).sum := by decide
  have hdescent : baseEnd_910176 < baseStart_910176 := by decide
  rcases family_descends (prefixWord ++ tailWord_910176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910180 : List Nat := [2, 3, 1, 1, 4, 2, 2, 1, 3, 3]
def baseStart_910180 : Nat := 118140960795 + 910180 * 2 ^ 59
def prefixEnd_910180 : Nat := 4983230072969 + 3 ^ 40 * 910180 * 2
def baseEnd_910180 : Nat := 311573214739569433509443

theorem tailTrace_910180 : CollatzResearch.WordTrace tailWord_910180 prefixEnd_910180 311573214739569433509443 := by
  unfold tailWord_910180
  simp only [CollatzResearch.WordTrace]
  refine ⟨16598495921290390606695997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22131327895053854142261329 16598495921290390606695997)
  ·
    refine ⟨6224435970483896477510999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16598495921290390606695997 6224435970483896477510999)
    ·
      refine ⟨9336653955725844716266499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6224435970483896477510999 9336653955725844716266499)
      ·
        refine ⟨14004980933588767074399749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9336653955725844716266499 14004980933588767074399749)
        ·
          refine ⟨2625933925047893826449953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14004980933588767074399749 2625933925047893826449953)
          ·
            refine ⟨1969450443785920369837465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2625933925047893826449953 1969450443785920369837465)
            ·
              refine ⟨1477087832839440277378099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1969450443785920369837465 1477087832839440277378099)
              ·
                refine ⟨2215631749259160416067149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1477087832839440277378099 2215631749259160416067149)
                ·
                  refine ⟨830861905972185156025181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2215631749259160416067149 830861905972185156025181)
                  ·
                    refine ⟨311573214739569433509443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 830861905972185156025181 311573214739569433509443)
                    ·
                      rfl

theorem cell22_910180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 1, 3, 3].length) (baseStart_910180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_910180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_910180 prefixEnd_910180 := by exact prefixLift 910180
  have htrace : WordTrace (prefixWord ++ tailWord_910180) baseStart_910180 baseEnd_910180 := by
    simpa [prefixWord, tailWord_910180, baseEnd_910180] using wordTrace_append hprefix tailTrace_910180
  have hstable : (prefixWord ++ tailWord_910180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910180).length < 2 ^ (prefixWord ++ tailWord_910180).sum := by decide
  have hdescent : baseEnd_910180 < baseStart_910180 := by decide
  rcases family_descends (prefixWord ++ tailWord_910180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910257 : List Nat := [1, 2, 2, 4, 3, 2, 1, 2, 1, 4]
def baseStart_910257 : Nat := 118140960795 + 910257 * 2 ^ 59
def prefixEnd_910257 : Nat := 4983230072969 + 3 ^ 40 * 910257 * 2
def baseEnd_910257 : Nat := 311599573413166899334207

theorem tailTrace_910257 : CollatzResearch.WordTrace tailWord_910257 prefixEnd_910257 311599573413166899334207 := by
  unfold tailWord_910257
  simp only [CollatzResearch.WordTrace]
  refine ⟨33199800263301823363945025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22133200175534548909296683 33199800263301823363945025)
  ·
    refine ⟨24899850197476367522958769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33199800263301823363945025 24899850197476367522958769)
    ·
      refine ⟨18674887648107275642219077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24899850197476367522958769 18674887648107275642219077)
      ·
        refine ⟨3501541434020114182916077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18674887648107275642219077 3501541434020114182916077)
        ·
          refine ⟨1313078037757542818593529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3501541434020114182916077 1313078037757542818593529)
          ·
            refine ⟨984808528318157113945147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1313078037757542818593529 984808528318157113945147)
            ·
              refine ⟨1477212792477235670917721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 984808528318157113945147 1477212792477235670917721)
              ·
                refine ⟨1107909594357926753188291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1477212792477235670917721 1107909594357926753188291)
                ·
                  refine ⟨1661864391536890129782437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1107909594357926753188291 1661864391536890129782437)
                  ·
                    refine ⟨311599573413166899334207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1661864391536890129782437 311599573413166899334207)
                    ·
                      rfl

theorem cell22_910257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 2, 1, 4].length) (baseStart_910257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_910257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_910257 prefixEnd_910257 := by exact prefixLift 910257
  have htrace : WordTrace (prefixWord ++ tailWord_910257) baseStart_910257 baseEnd_910257 := by
    simpa [prefixWord, tailWord_910257, baseEnd_910257] using wordTrace_append hprefix tailTrace_910257
  have hstable : (prefixWord ++ tailWord_910257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910257).length < 2 ^ (prefixWord ++ tailWord_910257).sum := by decide
  have hdescent : baseEnd_910257 < baseStart_910257 := by decide
  rcases family_descends (prefixWord ++ tailWord_910257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910266 : List Nat := [3, 1, 1, 1, 2, 1, 3, 10]
def baseStart_910266 : Nat := 118140960795 + 910266 * 2 ^ 59
def prefixEnd_910266 : Nat := 4983230072969 + 3 ^ 40 * 910266 * 2
def baseEnd_910266 : Nat := 34622517144121541762131

theorem tailTrace_910266 : CollatzResearch.WordTrace tailWord_910266 prefixEnd_910266 34622517144121541762131 := by
  unfold tailWord_910266
  simp only [CollatzResearch.WordTrace]
  refine ⟨8300032130067304475255663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22133419013512811934015101 8300032130067304475255663)
  ·
    refine ⟨12450048195100956712883495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8300032130067304475255663 12450048195100956712883495)
    ·
      refine ⟨18675072292651435069325243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12450048195100956712883495 18675072292651435069325243)
      ·
        refine ⟨28012608438977152603987865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18675072292651435069325243 28012608438977152603987865)
        ·
          refine ⟨21009456329232864452990899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28012608438977152603987865 21009456329232864452990899)
          ·
            refine ⟨31514184493849296679486349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21009456329232864452990899 31514184493849296679486349)
            ·
              refine ⟨11817819185193486254807381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31514184493849296679486349 11817819185193486254807381)
              ·
                refine ⟨34622517144121541762131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 11817819185193486254807381 34622517144121541762131)
                ·
                  rfl

theorem cell22_910266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 10].length) (baseStart_910266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_910266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_910266 prefixEnd_910266 := by exact prefixLift 910266
  have htrace : WordTrace (prefixWord ++ tailWord_910266) baseStart_910266 baseEnd_910266 := by
    simpa [prefixWord, tailWord_910266, baseEnd_910266] using wordTrace_append hprefix tailTrace_910266
  have hstable : (prefixWord ++ tailWord_910266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910266).length < 2 ^ (prefixWord ++ tailWord_910266).sum := by decide
  have hdescent : baseEnd_910266 < baseStart_910266 := by decide
  rcases family_descends (prefixWord ++ tailWord_910266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910332 : List Nat := [2, 2, 2, 1, 2, 3, 1, 5, 1, 3]
def baseStart_910332 : Nat := 118140960795 + 910332 * 2 ^ 59
def prefixEnd_910332 : Nat := 4983230072969 + 3 ^ 40 * 910332 * 2
def baseEnd_910332 : Nat := 311625247445891703708977

theorem tailTrace_910332 : CollatzResearch.WordTrace tailWord_910332 prefixEnd_910332 311625247445891703708977 := by
  unfold tailWord_910332
  simp only [CollatzResearch.WordTrace]
  refine ⟨16601267869015055586462625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22135023825353407448616833 16601267869015055586462625)
  ·
    refine ⟨12450950901761291689846969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16601267869015055586462625 12450950901761291689846969)
    ·
      refine ⟨9338213176320968767385227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12450950901761291689846969 9338213176320968767385227)
      ·
        refine ⟨14007319764481453151077841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9338213176320968767385227 14007319764481453151077841)
        ·
          refine ⟨10505489823361089863308381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14007319764481453151077841 10505489823361089863308381)
          ·
            refine ⟨3939558683760408698740643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10505489823361089863308381 3939558683760408698740643)
            ·
              refine ⟨5909338025640613048110965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3939558683760408698740643 5909338025640613048110965)
              ·
                refine ⟨554000439903807473260403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5909338025640613048110965 554000439903807473260403)
                ·
                  refine ⟨831000659855711209890605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 554000439903807473260403 831000659855711209890605)
                  ·
                    refine ⟨311625247445891703708977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 831000659855711209890605 311625247445891703708977)
                    ·
                      rfl

theorem cell22_910332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 5, 1, 3].length) (baseStart_910332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_910332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_910332 prefixEnd_910332 := by exact prefixLift 910332
  have htrace : WordTrace (prefixWord ++ tailWord_910332) baseStart_910332 baseEnd_910332 := by
    simpa [prefixWord, tailWord_910332, baseEnd_910332] using wordTrace_append hprefix tailTrace_910332
  have hstable : (prefixWord ++ tailWord_910332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910332).length < 2 ^ (prefixWord ++ tailWord_910332).sum := by decide
  have hdescent : baseEnd_910332 < baseStart_910332 := by decide
  rcases family_descends (prefixWord ++ tailWord_910332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910338 : List Nat := [3, 4, 1, 3, 2, 1, 1, 2, 2, 3]
def baseStart_910338 : Nat := 118140960795 + 910338 * 2 ^ 59
def prefixEnd_910338 : Nat := 4983230072969 + 3 ^ 40 * 910338 * 2
def baseEnd_910338 : Nat := 311627301368509688058959

theorem tailTrace_910338 : CollatzResearch.WordTrace tailWord_910338 prefixEnd_910338 311627301368509688058959 := by
  unfold tailWord_910338
  simp only [CollatzResearch.WordTrace]
  refine ⟨8300688644002093549410917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22135169717338916131762445 8300688644002093549410917)
  ·
    refine ⟨1556379120750392540514547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8300688644002093549410917 1556379120750392540514547)
    ·
      refine ⟨2334568681125588810771821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1556379120750392540514547 2334568681125588810771821)
      ·
        refine ⟨875463255422095804039433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2334568681125588810771821 875463255422095804039433)
        ·
          refine ⟨656597441566571853029575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 875463255422095804039433 656597441566571853029575)
          ·
            refine ⟨984896162349857779544363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 656597441566571853029575 984896162349857779544363)
            ·
              refine ⟨1477344243524786669316545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 984896162349857779544363 1477344243524786669316545)
              ·
                refine ⟨1108008182643590001987409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1477344243524786669316545 1108008182643590001987409)
                ·
                  refine ⟨831006136982692501490557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1108008182643590001987409 831006136982692501490557)
                  ·
                    refine ⟨311627301368509688058959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 831006136982692501490557 311627301368509688058959)
                    ·
                      rfl

theorem cell22_910338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_910338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_910338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_910338 prefixEnd_910338 := by exact prefixLift 910338
  have htrace : WordTrace (prefixWord ++ tailWord_910338) baseStart_910338 baseEnd_910338 := by
    simpa [prefixWord, tailWord_910338, baseEnd_910338] using wordTrace_append hprefix tailTrace_910338
  have hstable : (prefixWord ++ tailWord_910338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910338).length < 2 ^ (prefixWord ++ tailWord_910338).sum := by decide
  have hdescent : baseEnd_910338 < baseStart_910338 := by decide
  rcases family_descends (prefixWord ++ tailWord_910338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910343 : List Nat := [1, 1, 4, 3, 1, 1, 1, 1, 4, 5]
def baseStart_910343 : Nat := 118140960795 + 910343 * 2 ^ 59
def prefixEnd_910343 : Nat := 4983230072969 + 3 ^ 40 * 910343 * 2
def baseEnd_910343 : Nat := 311629012970691341683943

theorem tailTrace_910343 : CollatzResearch.WordTrace tailWord_910343 prefixEnd_910343 311629012970691341683943 := by
  unfold tailWord_910343
  simp only [CollatzResearch.WordTrace]
  refine ⟨33202936940990260051575683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22135291293993506701050455 33202936940990260051575683)
  ·
    refine ⟨49804405411485390077363525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33202936940990260051575683 49804405411485390077363525)
    ·
      refine ⟨9338326014653510639505661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49804405411485390077363525 9338326014653510639505661)
      ·
        refine ⟨3501872255495066489814623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9338326014653510639505661 3501872255495066489814623)
        ·
          refine ⟨5252808383242599734721935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3501872255495066489814623 5252808383242599734721935)
          ·
            refine ⟨7879212574863899602082903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5252808383242599734721935 7879212574863899602082903)
            ·
              refine ⟨11818818862295849403124355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7879212574863899602082903 11818818862295849403124355)
              ·
                refine ⟨17728228293443774104686533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11818818862295849403124355 17728228293443774104686533)
                ·
                  refine ⟨3324042805020707644628725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17728228293443774104686533 3324042805020707644628725)
                  ·
                    refine ⟨311629012970691341683943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3324042805020707644628725 311629012970691341683943)
                    ·
                      rfl

theorem cell22_910343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_910343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_910343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_910343 prefixEnd_910343 := by exact prefixLift 910343
  have htrace : WordTrace (prefixWord ++ tailWord_910343) baseStart_910343 baseEnd_910343 := by
    simpa [prefixWord, tailWord_910343, baseEnd_910343] using wordTrace_append hprefix tailTrace_910343
  have hstable : (prefixWord ++ tailWord_910343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910343).length < 2 ^ (prefixWord ++ tailWord_910343).sum := by decide
  have hdescent : baseEnd_910343 < baseStart_910343 := by decide
  rcases family_descends (prefixWord ++ tailWord_910343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910373 : List Nat := [1, 3, 1, 2, 2, 2, 1, 4, 6]
def baseStart_910373 : Nat := 118140960795 + 910373 * 2 ^ 59
def prefixEnd_910373 : Nat := 4983230072969 + 3 ^ 40 * 910373 * 2
def baseEnd_910373 : Nat := 103879760861260421144617

theorem tailTrace_910373 : CollatzResearch.WordTrace tailWord_910373 prefixEnd_910373 103879760861260421144617 := by
  unfold tailWord_910373
  simp only [CollatzResearch.WordTrace]
  refine ⟨33204031130881575175167773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22136020753921050116778515 33204031130881575175167773)
  ·
    refine ⟨12451511674080590690687915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33204031130881575175167773 12451511674080590690687915)
    ·
      refine ⟨18677267511120886036031873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12451511674080590690687915 18677267511120886036031873)
      ·
        refine ⟨14007950633340664527023905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18677267511120886036031873 14007950633340664527023905)
        ·
          refine ⟨10505962975005498395267929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14007950633340664527023905 10505962975005498395267929)
          ·
            refine ⟨7879472231254123796450947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10505962975005498395267929 7879472231254123796450947)
            ·
              refine ⟨11819208346881185694676421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7879472231254123796450947 11819208346881185694676421)
              ·
                refine ⟨2216101565040222317751829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11819208346881185694676421 2216101565040222317751829)
                ·
                  refine ⟨103879760861260421144617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2216101565040222317751829 103879760861260421144617)
                  ·
                    rfl

theorem cell22_910373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4, 6].length) (baseStart_910373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_910373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_910373 prefixEnd_910373 := by exact prefixLift 910373
  have htrace : WordTrace (prefixWord ++ tailWord_910373) baseStart_910373 baseEnd_910373 := by
    simpa [prefixWord, tailWord_910373, baseEnd_910373] using wordTrace_append hprefix tailTrace_910373
  have hstable : (prefixWord ++ tailWord_910373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910373).length < 2 ^ (prefixWord ++ tailWord_910373).sum := by decide
  have hdescent : baseEnd_910373 < baseStart_910373 := by decide
  rcases family_descends (prefixWord ++ tailWord_910373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910405 : List Nat := [1, 3, 1, 1, 1, 3, 4, 1, 4, 3]
def baseStart_910405 : Nat := 118140960795 + 910405 * 2 ^ 59
def prefixEnd_910405 : Nat := 4983230072969 + 3 ^ 40 * 910405 * 2
def baseEnd_910405 : Nat := 311650236837743846633753

theorem tailTrace_910405 : CollatzResearch.WordTrace tailWord_910405 prefixEnd_910405 311650236837743846633753 := by
  unfold tailWord_910405
  simp only [CollatzResearch.WordTrace]
  refine ⟨33205198266765644640332669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22136798844510429760221779 33205198266765644640332669)
  ·
    refine ⟨12451949350037116740124751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33205198266765644640332669 12451949350037116740124751)
    ·
      refine ⟨18677924025055675110187127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12451949350037116740124751 18677924025055675110187127)
      ·
        refine ⟨28016886037583512665280691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18677924025055675110187127 28016886037583512665280691)
        ·
          refine ⟨42025329056375268997921037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28016886037583512665280691 42025329056375268997921037)
          ·
            refine ⟨15759498396140725874220389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42025329056375268997921037 15759498396140725874220389)
            ·
              refine ⟨2954905949276386101416323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15759498396140725874220389 2954905949276386101416323)
              ·
                refine ⟨4432358923914579152124485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2954905949276386101416323 4432358923914579152124485)
                ·
                  refine ⟨831067298233983591023341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4432358923914579152124485 831067298233983591023341)
                  ·
                    refine ⟨311650236837743846633753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 831067298233983591023341 311650236837743846633753)
                    ·
                      rfl

theorem cell22_910405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 4, 3].length) (baseStart_910405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_910405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_910405 prefixEnd_910405 := by exact prefixLift 910405
  have htrace : WordTrace (prefixWord ++ tailWord_910405) baseStart_910405 baseEnd_910405 := by
    simpa [prefixWord, tailWord_910405, baseEnd_910405] using wordTrace_append hprefix tailTrace_910405
  have hstable : (prefixWord ++ tailWord_910405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910405).length < 2 ^ (prefixWord ++ tailWord_910405).sum := by decide
  have hdescent : baseEnd_910405 < baseStart_910405 := by decide
  rcases family_descends (prefixWord ++ tailWord_910405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910433 : List Nat := [1, 2, 3, 1, 1, 2, 2, 1, 2, 7]
def baseStart_910433 : Nat := 118140960795 + 910433 * 2 ^ 59
def prefixEnd_910433 : Nat := 4983230072969 + 3 ^ 40 * 910433 * 2
def baseEnd_910433 : Nat := 311659821809961106933667

theorem tailTrace_910433 : CollatzResearch.WordTrace tailWord_910433 prefixEnd_910433 311659821809961106933667 := by
  unfold tailWord_910433
  simp only [CollatzResearch.WordTrace]
  refine ⟨33206219510664205422351953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22137479673776136948234635 33206219510664205422351953)
  ·
    refine ⟨24904664632998154066763965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33206219510664205422351953 24904664632998154066763965)
    ·
      refine ⟨9339249237374307775036487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24904664632998154066763965 9339249237374307775036487)
      ·
        refine ⟨14008873856061461662554731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9339249237374307775036487 14008873856061461662554731)
        ·
          refine ⟨21013310784092192493832097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14008873856061461662554731 21013310784092192493832097)
          ·
            refine ⟨15759983088069144370374073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21013310784092192493832097 15759983088069144370374073)
            ·
              refine ⟨11819987316051858277780555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15759983088069144370374073 11819987316051858277780555)
              ·
                refine ⟨17729980974077787416670833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11819987316051858277780555 17729980974077787416670833)
                ·
                  refine ⟨13297485730558340562503125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17729980974077787416670833 13297485730558340562503125)
                  ·
                    refine ⟨311659821809961106933667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13297485730558340562503125 311659821809961106933667)
                    ·
                      rfl

theorem cell22_910433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_910433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_910433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_910433 prefixEnd_910433 := by exact prefixLift 910433
  have htrace : WordTrace (prefixWord ++ tailWord_910433) baseStart_910433 baseEnd_910433 := by
    simpa [prefixWord, tailWord_910433, baseEnd_910433] using wordTrace_append hprefix tailTrace_910433
  have hstable : (prefixWord ++ tailWord_910433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910433).length < 2 ^ (prefixWord ++ tailWord_910433).sum := by decide
  have hdescent : baseEnd_910433 < baseStart_910433 := by decide
  rcases family_descends (prefixWord ++ tailWord_910433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910465 : List Nat := [1, 2, 4, 2, 2, 1, 1, 1, 2, 6]
def baseStart_910465 : Nat := 118140960795 + 910465 * 2 ^ 59
def prefixEnd_910465 : Nat := 4983230072969 + 3 ^ 40 * 910465 * 2
def baseEnd_910465 : Nat := 311670776063923690133569

theorem tailTrace_910465 : CollatzResearch.WordTrace tailWord_910465 prefixEnd_910465 311670776063923690133569 := by
  unfold tailWord_910465
  simp only [CollatzResearch.WordTrace]
  refine ⟨33207386646548274887516849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22138257764365516591677899 33207386646548274887516849)
  ·
    refine ⟨24905539984911206165637637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33207386646548274887516849 24905539984911206165637637)
    ·
      refine ⟨4669788747170851156057057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24905539984911206165637637 4669788747170851156057057)
      ·
        refine ⟨3502341560378138367042793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4669788747170851156057057 3502341560378138367042793)
        ·
          refine ⟨2626756170283603775282095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3502341560378138367042793 2626756170283603775282095)
          ·
            refine ⟨3940134255425405662923143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2626756170283603775282095 3940134255425405662923143)
            ·
              refine ⟨5910201383138108494384715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3940134255425405662923143 5910201383138108494384715)
              ·
                refine ⟨8865302074707162741577073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5910201383138108494384715 8865302074707162741577073)
                ·
                  refine ⟨6648976556030372056182805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8865302074707162741577073 6648976556030372056182805)
                  ·
                    refine ⟨311670776063923690133569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6648976556030372056182805 311670776063923690133569)
                    ·
                      rfl

theorem cell22_910465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_910465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_910465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_910465 prefixEnd_910465 := by exact prefixLift 910465
  have htrace : WordTrace (prefixWord ++ tailWord_910465) baseStart_910465 baseEnd_910465 := by
    simpa [prefixWord, tailWord_910465, baseEnd_910465] using wordTrace_append hprefix tailTrace_910465
  have hstable : (prefixWord ++ tailWord_910465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910465).length < 2 ^ (prefixWord ++ tailWord_910465).sum := by decide
  have hdescent : baseEnd_910465 < baseStart_910465 := by decide
  rcases family_descends (prefixWord ++ tailWord_910465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910518 : List Nat := [5, 1, 3, 2, 1, 1, 2, 1, 3, 3]
def baseStart_910518 : Nat := 118140960795 + 910518 * 2 ^ 59
def prefixEnd_910518 : Nat := 4983230072969 + 3 ^ 40 * 910518 * 2
def baseEnd_910518 : Nat := 311688919047049218558407

theorem tailTrace_910518 : CollatzResearch.WordTrace tailWord_910518 prefixEnd_910518 311688919047049218558407 := by
  unfold tailWord_910518
  simp only [CollatzResearch.WordTrace]
  refine ⟨2075582482209766558699763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22139546476904176626130805 2075582482209766558699763)
  ·
    refine ⟨3113373723314649838049645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2075582482209766558699763 3113373723314649838049645)
    ·
      refine ⟨1167515146242993689268617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3113373723314649838049645 1167515146242993689268617)
      ·
        refine ⟨875636359682245266951463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1167515146242993689268617 875636359682245266951463)
        ·
          refine ⟨1313454539523367900427195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 875636359682245266951463 1313454539523367900427195)
          ·
            refine ⟨1970181809285051850640793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1313454539523367900427195 1970181809285051850640793)
            ·
              refine ⟨1477636356963788887980595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1970181809285051850640793 1477636356963788887980595)
              ·
                refine ⟨2216454535445683331970893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1477636356963788887980595 2216454535445683331970893)
                ·
                  refine ⟨831170450792131249489085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2216454535445683331970893 831170450792131249489085)
                  ·
                    refine ⟨311688919047049218558407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 831170450792131249489085 311688919047049218558407)
                    ·
                      rfl

theorem cell22_910518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_910518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_910518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_910518 prefixEnd_910518 := by exact prefixLift 910518
  have htrace : WordTrace (prefixWord ++ tailWord_910518) baseStart_910518 baseEnd_910518 := by
    simpa [prefixWord, tailWord_910518, baseEnd_910518] using wordTrace_append hprefix tailTrace_910518
  have hstable : (prefixWord ++ tailWord_910518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910518).length < 2 ^ (prefixWord ++ tailWord_910518).sum := by decide
  have hdescent : baseEnd_910518 < baseStart_910518 := by decide
  rcases family_descends (prefixWord ++ tailWord_910518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910525 : List Nat := [1, 4, 1, 2, 1, 1, 3, 3, 6]
def baseStart_910525 : Nat := 118140960795 + 910525 * 2 ^ 59
def prefixEnd_910525 : Nat := 4983230072969 + 3 ^ 40 * 910525 * 2
def baseEnd_910525 : Nat := 103897105096701177877795

theorem tailTrace_910525 : CollatzResearch.WordTrace tailWord_910525 prefixEnd_910525 103897105096701177877795 := by
  unfold tailWord_910525
  simp only [CollatzResearch.WordTrace]
  refine ⟨33209575026330905134701029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22139716684220603423134019 33209575026330905134701029)
  ·
    refine ⟨6226795317437044712756443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33209575026330905134701029 6226795317437044712756443)
    ·
      refine ⟨9340192976155567069134665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6226795317437044712756443 9340192976155567069134665)
      ·
        refine ⟨7005144732116675301850999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9340192976155567069134665 7005144732116675301850999)
        ·
          refine ⟨10507717098175012952776499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7005144732116675301850999 10507717098175012952776499)
          ·
            refine ⟨15761575647262519429164749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10507717098175012952776499 15761575647262519429164749)
            ·
              refine ⟨5910590867723444785936781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15761575647262519429164749 5910590867723444785936781)
              ·
                refine ⟨2216471575396291794726293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5910590867723444785936781 2216471575396291794726293)
                ·
                  refine ⟨103897105096701177877795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2216471575396291794726293 103897105096701177877795)
                  ·
                    rfl

theorem cell22_910525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3, 6].length) (baseStart_910525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_910525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_910525 prefixEnd_910525 := by exact prefixLift 910525
  have htrace : WordTrace (prefixWord ++ tailWord_910525) baseStart_910525 baseEnd_910525 := by
    simpa [prefixWord, tailWord_910525, baseEnd_910525] using wordTrace_append hprefix tailTrace_910525
  have hstable : (prefixWord ++ tailWord_910525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910525).length < 2 ^ (prefixWord ++ tailWord_910525).sum := by decide
  have hdescent : baseEnd_910525 < baseStart_910525 := by decide
  rcases family_descends (prefixWord ++ tailWord_910525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910570 : List Nat := [3, 1, 3, 1, 1, 3, 10]
def baseStart_910570 : Nat := 118140960795 + 910570 * 2 ^ 59
def prefixEnd_910570 : Nat := 4983230072969 + 3 ^ 40 * 910570 * 2
def baseEnd_910570 : Nat := 11544693322582904305861

theorem tailTrace_910570 : CollatzResearch.WordTrace tailWord_910570 prefixEnd_910570 11544693322582904305861 := by
  unfold tailWord_910570
  simp only [CollatzResearch.WordTrace]
  refine ⟨8302804077791969455022291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22140810874111918546726109 8302804077791969455022291)
  ·
    refine ⟨12454206116687954182533437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8302804077791969455022291 12454206116687954182533437)
    ·
      refine ⟨4670327293757982818450039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12454206116687954182533437 4670327293757982818450039)
      ·
        refine ⟨7005490940636974227675059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4670327293757982818450039 7005490940636974227675059)
        ·
          refine ⟨10508236410955461341512589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7005490940636974227675059 10508236410955461341512589)
          ·
            refine ⟨3940588654108298003067221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10508236410955461341512589 3940588654108298003067221)
            ·
              refine ⟨11544693322582904305861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3940588654108298003067221 11544693322582904305861)
              ·
                rfl

theorem cell22_910570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 10].length) (baseStart_910570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_910570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_910570 prefixEnd_910570 := by exact prefixLift 910570
  have htrace : WordTrace (prefixWord ++ tailWord_910570) baseStart_910570 baseEnd_910570 := by
    simpa [prefixWord, tailWord_910570, baseEnd_910570] using wordTrace_append hprefix tailTrace_910570
  have hstable : (prefixWord ++ tailWord_910570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910570).length < 2 ^ (prefixWord ++ tailWord_910570).sum := by decide
  have hdescent : baseEnd_910570 < baseStart_910570 := by decide
  rcases family_descends (prefixWord ++ tailWord_910570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910572 : List Nat := [2, 2, 1, 1, 2, 5, 1, 2, 2, 4]
def baseStart_910572 : Nat := 118140960795 + 910572 * 2 ^ 59
def prefixEnd_910572 : Nat := 4983230072969 + 3 ^ 40 * 910572 * 2
def baseEnd_910572 : Nat := 311707404350611077708241

theorem tailTrace_910572 : CollatzResearch.WordTrace tailWord_910572 prefixEnd_910572 311707404350611077708241 := by
  unfold tailWord_910572
  simp only [CollatzResearch.WordTrace]
  refine ⟨16605644628580316080830985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22140859504773754774441313 16605644628580316080830985)
  ·
    refine ⟨12454233471435237060623239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16605644628580316080830985 12454233471435237060623239)
    ·
      refine ⟨18681350207152855590934859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12454233471435237060623239 18681350207152855590934859)
      ·
        refine ⟨28022025310729283386402289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18681350207152855590934859 28022025310729283386402289)
        ·
          refine ⟨21016518983046962539801717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28022025310729283386402289 21016518983046962539801717)
          ·
            refine ⟨1970298654660652738106411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21016518983046962539801717 1970298654660652738106411)
            ·
              refine ⟨2955447981990979107159617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1970298654660652738106411 2955447981990979107159617)
              ·
                refine ⟨2216585986493234330369713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2955447981990979107159617 2216585986493234330369713)
                ·
                  refine ⟨1662439489869925747777285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2216585986493234330369713 1662439489869925747777285)
                  ·
                    refine ⟨311707404350611077708241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1662439489869925747777285 311707404350611077708241)
                    ·
                      rfl

theorem cell22_910572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 4].length) (baseStart_910572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_910572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_910572 prefixEnd_910572 := by exact prefixLift 910572
  have htrace : WordTrace (prefixWord ++ tailWord_910572) baseStart_910572 baseEnd_910572 := by
    simpa [prefixWord, tailWord_910572, baseEnd_910572] using wordTrace_append hprefix tailTrace_910572
  have hstable : (prefixWord ++ tailWord_910572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910572).length < 2 ^ (prefixWord ++ tailWord_910572).sum := by decide
  have hdescent : baseEnd_910572 < baseStart_910572 := by decide
  rcases family_descends (prefixWord ++ tailWord_910572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910591 : List Nat := [1, 1, 2, 2, 1, 7, 2, 1, 2, 3]
def baseStart_910591 : Nat := 118140960795 + 910591 * 2 ^ 59
def prefixEnd_910591 : Nat := 4983230072969 + 3 ^ 40 * 910591 * 2
def baseEnd_910591 : Nat := 311713908438901361483183

theorem tailTrace_910591 : CollatzResearch.WordTrace tailWord_910591 prefixEnd_910591 311713908438901361483183 := by
  unfold tailWord_910591
  simp only [CollatzResearch.WordTrace]
  refine ⟨33211982244091798406603627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22141321496061198937735751 33211982244091798406603627)
  ·
    refine ⟨49817973366137697609905441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33211982244091798406603627 49817973366137697609905441)
    ·
      refine ⟨37363480024603273207429081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49817973366137697609905441 37363480024603273207429081)
      ·
        refine ⟨28022610018452454905571811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37363480024603273207429081 28022610018452454905571811)
        ·
          refine ⟨42033915027678682358357717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28022610018452454905571811 42033915027678682358357717)
          ·
            refine ⟨985169883461219117774009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 42033915027678682358357717 985169883461219117774009)
            ·
              refine ⟨738877412595914338330507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 985169883461219117774009 738877412595914338330507)
              ·
                refine ⟨1108316118893871507495761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 738877412595914338330507 1108316118893871507495761)
                ·
                  refine ⟨831237089170403630621821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1108316118893871507495761 831237089170403630621821)
                  ·
                    refine ⟨311713908438901361483183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 831237089170403630621821 311713908438901361483183)
                    ·
                      rfl

theorem cell22_910591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 1, 2, 3].length) (baseStart_910591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_910591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_910591 prefixEnd_910591 := by exact prefixLift 910591
  have htrace : WordTrace (prefixWord ++ tailWord_910591) baseStart_910591 baseEnd_910591 := by
    simpa [prefixWord, tailWord_910591, baseEnd_910591] using wordTrace_append hprefix tailTrace_910591
  have hstable : (prefixWord ++ tailWord_910591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910591).length < 2 ^ (prefixWord ++ tailWord_910591).sum := by decide
  have hdescent : baseEnd_910591 < baseStart_910591 := by decide
  rcases family_descends (prefixWord ++ tailWord_910591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910602 : List Nat := [3, 1, 2, 2, 1, 1, 1, 3, 5, 3]
def baseStart_910602 : Nat := 118140960795 + 910602 * 2 ^ 59
def prefixEnd_910602 : Nat := 4983230072969 + 3 ^ 40 * 910602 * 2
def baseEnd_910602 : Nat := 311717673963700999458149

theorem tailTrace_910602 : CollatzResearch.WordTrace tailWord_910602 prefixEnd_910602 311717673963700999458149 := by
  unfold tailWord_910602
  simp only [CollatzResearch.WordTrace]
  refine ⟨8303095861762986821313515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22141588964701298190169373 8303095861762986821313515)
  ·
    refine ⟨12454643792644480231970273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8303095861762986821313515 12454643792644480231970273)
    ·
      refine ⟨9340982844483360173977705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12454643792644480231970273 9340982844483360173977705)
      ·
        refine ⟨7005737133362520130483279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9340982844483360173977705 7005737133362520130483279)
        ·
          refine ⟨10508605700043780195724919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7005737133362520130483279 10508605700043780195724919)
          ·
            refine ⟨15762908550065670293587379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10508605700043780195724919 15762908550065670293587379)
            ·
              refine ⟨23644362825098505440381069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15762908550065670293587379 23644362825098505440381069)
              ·
                refine ⟨8866636059411939540142901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23644362825098505440381069 8866636059411939540142901)
                ·
                  refine ⟨831247130569869331888397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8866636059411939540142901 831247130569869331888397)
                  ·
                    refine ⟨311717673963700999458149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 831247130569869331888397 311717673963700999458149)
                    ·
                      rfl

theorem cell22_910602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 5, 3].length) (baseStart_910602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_910602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_910602 prefixEnd_910602 := by exact prefixLift 910602
  have htrace : WordTrace (prefixWord ++ tailWord_910602) baseStart_910602 baseEnd_910602 := by
    simpa [prefixWord, tailWord_910602, baseEnd_910602] using wordTrace_append hprefix tailTrace_910602
  have hstable : (prefixWord ++ tailWord_910602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910602).length < 2 ^ (prefixWord ++ tailWord_910602).sum := by decide
  have hdescent : baseEnd_910602 < baseStart_910602 := by decide
  rcases family_descends (prefixWord ++ tailWord_910602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910619 : List Nat := [1, 1, 1, 1, 1, 1, 5, 7, 1, 3]
def baseStart_910619 : Nat := 118140960795 + 910619 * 2 ^ 59
def prefixEnd_910619 : Nat := 4983230072969 + 3 ^ 40 * 910619 * 2
def baseEnd_910619 : Nat := 311723493411118621783097

theorem tailTrace_910619 : CollatzResearch.WordTrace tailWord_910619 prefixEnd_910619 311723493411118621783097 := by
  unfold tailWord_910619
  simp only [CollatzResearch.WordTrace]
  refine ⟨33213003487990359188622911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22142002325326906125748607 33213003487990359188622911)
  ·
    refine ⟨49819505231985538782934367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33213003487990359188622911 49819505231985538782934367)
    ·
      refine ⟨74729257847978308174401551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49819505231985538782934367 74729257847978308174401551)
      ·
        refine ⟨112093886771967462261602327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74729257847978308174401551 112093886771967462261602327)
        ·
          refine ⟨168140830157951193392403491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112093886771967462261602327 168140830157951193392403491)
          ·
            refine ⟨252211245236926790088605237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168140830157951193392403491 252211245236926790088605237)
            ·
              refine ⟨23644804240961886570806741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 252211245236926790088605237 23644804240961886570806741)
              ·
                refine ⟨554175099397544216503283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 23644804240961886570806741 554175099397544216503283)
                ·
                  refine ⟨831262649096316324754925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 554175099397544216503283 831262649096316324754925)
                  ·
                    refine ⟨311723493411118621783097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 831262649096316324754925 311723493411118621783097)
                    ·
                      rfl

theorem cell22_910619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7, 1, 3].length) (baseStart_910619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_910619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_910619 prefixEnd_910619 := by exact prefixLift 910619
  have htrace : WordTrace (prefixWord ++ tailWord_910619) baseStart_910619 baseEnd_910619 := by
    simpa [prefixWord, tailWord_910619, baseEnd_910619] using wordTrace_append hprefix tailTrace_910619
  have hstable : (prefixWord ++ tailWord_910619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910619).length < 2 ^ (prefixWord ++ tailWord_910619).sum := by decide
  have hdescent : baseEnd_910619 < baseStart_910619 := by decide
  rcases family_descends (prefixWord ++ tailWord_910619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910679 : List Nat := [1, 1, 3, 2, 3, 3, 1, 3, 1, 4]
def baseStart_910679 : Nat := 118140960795 + 910679 * 2 ^ 59
def prefixEnd_910679 : Nat := 4983230072969 + 3 ^ 40 * 910679 * 2
def baseEnd_910679 : Nat := 311744032637298465282913

theorem tailTrace_910679 : CollatzResearch.WordTrace tailWord_910679 prefixEnd_910679 311744032637298465282913 := by
  unfold tailWord_910679
  simp only [CollatzResearch.WordTrace]
  refine ⟨33215191867772989435807091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22143461245181992957204727 33215191867772989435807091)
  ·
    refine ⟨49822787801659484153710637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33215191867772989435807091 49822787801659484153710637)
    ·
      refine ⟨18683545425622306557641489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49822787801659484153710637 18683545425622306557641489)
      ·
        refine ⟨14012659069216729918231117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18683545425622306557641489 14012659069216729918231117)
        ·
          refine ⟨5254747150956273719336669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14012659069216729918231117 5254747150956273719336669)
          ·
            refine ⟨1970530181608602644751251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5254747150956273719336669 1970530181608602644751251)
            ·
              refine ⟨2955795272412903967126877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1970530181608602644751251 2955795272412903967126877)
              ·
                refine ⟨1108423227154838987672579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2955795272412903967126877 1108423227154838987672579)
                ·
                  refine ⟨1662634840732258481508869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1108423227154838987672579 1662634840732258481508869)
                  ·
                    refine ⟨311744032637298465282913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1662634840732258481508869 311744032637298465282913)
                    ·
                      rfl

theorem cell22_910679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 3, 1, 4].length) (baseStart_910679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_910679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_910679 prefixEnd_910679 := by exact prefixLift 910679
  have htrace : WordTrace (prefixWord ++ tailWord_910679) baseStart_910679 baseEnd_910679 := by
    simpa [prefixWord, tailWord_910679, baseEnd_910679] using wordTrace_append hprefix tailTrace_910679
  have hstable : (prefixWord ++ tailWord_910679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910679).length < 2 ^ (prefixWord ++ tailWord_910679).sum := by decide
  have hdescent : baseEnd_910679 < baseStart_910679 := by decide
  rcases family_descends (prefixWord ++ tailWord_910679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910752 : List Nat := [2, 1, 1, 4, 1, 2, 2, 1, 2, 6]
def baseStart_910752 : Nat := 118140960795 + 910752 * 2 ^ 59
def prefixEnd_910752 : Nat := 4983230072969 + 3 ^ 40 * 910752 * 2
def baseEnd_910752 : Nat := 311769022029150608207689

theorem tailTrace_910752 : CollatzResearch.WordTrace tailWord_910752 prefixEnd_910752 311769022029150608207689 := by
  unfold tailWord_910752
  simp only [CollatzResearch.WordTrace]
  refine ⟨16608927198254261451607255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22145236264339015268809673 16608927198254261451607255)
  ·
    refine ⟨24913390797381392177410883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16608927198254261451607255 24913390797381392177410883)
    ·
      refine ⟨37370086196072088266116325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24913390797381392177410883 37370086196072088266116325)
      ·
        refine ⟨7006891161763516549896811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37370086196072088266116325 7006891161763516549896811)
        ·
          refine ⟨10510336742645274824845217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7006891161763516549896811 10510336742645274824845217)
          ·
            refine ⟨7882752556983956118633913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10510336742645274824845217 7882752556983956118633913)
            ·
              refine ⟨5912064417737967088975435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7882752556983956118633913 5912064417737967088975435)
              ·
                refine ⟨8868096626606950633463153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5912064417737967088975435 8868096626606950633463153)
                ·
                  refine ⟨6651072469955212975097365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8868096626606950633463153 6651072469955212975097365)
                  ·
                    refine ⟨311769022029150608207689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6651072469955212975097365 311769022029150608207689)
                    ·
                      rfl

theorem cell22_910752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 2, 6].length) (baseStart_910752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_910752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_910752 prefixEnd_910752 := by exact prefixLift 910752
  have htrace : WordTrace (prefixWord ++ tailWord_910752) baseStart_910752 baseEnd_910752 := by
    simpa [prefixWord, tailWord_910752, baseEnd_910752] using wordTrace_append hprefix tailTrace_910752
  have hstable : (prefixWord ++ tailWord_910752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910752).length < 2 ^ (prefixWord ++ tailWord_910752).sum := by decide
  have hdescent : baseEnd_910752 < baseStart_910752 := by decide
  rcases family_descends (prefixWord ++ tailWord_910752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910844 : List Nat := [2, 2, 2, 1, 2, 1, 4, 2, 1, 5]
def baseStart_910844 : Nat := 118140960795 + 910844 * 2 ^ 59
def prefixEnd_910844 : Nat := 4983230072969 + 3 ^ 40 * 910844 * 2
def baseEnd_910844 : Nat := 311800515509293034907407

theorem tailTrace_910844 : CollatzResearch.WordTrace tailWord_910844 prefixEnd_910844 311800515509293034907407 := by
  unfold tailWord_910844
  simp only [CollatzResearch.WordTrace]
  refine ⟨16610604956087611307781793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22147473274783481743709057 16610604956087611307781793)
  ·
    refine ⟨12457953717065708480836345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16610604956087611307781793 12457953717065708480836345)
    ·
      refine ⟨9343465287799281360627259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12457953717065708480836345 9343465287799281360627259)
      ·
        refine ⟨14015197931698922040940889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9343465287799281360627259 14015197931698922040940889)
        ·
          refine ⟨10511398448774191530705667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14015197931698922040940889 10511398448774191530705667)
          ·
            refine ⟨15767097673161287296058501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10511398448774191530705667 15767097673161287296058501)
            ·
              refine ⟨2956330813717741368010969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15767097673161287296058501 2956330813717741368010969)
              ·
                refine ⟨2217248110288306026008227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2956330813717741368010969 2217248110288306026008227)
                ·
                  refine ⟨3325872165432459039012341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2217248110288306026008227 3325872165432459039012341)
                  ·
                    refine ⟨311800515509293034907407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3325872165432459039012341 311800515509293034907407)
                    ·
                      rfl

theorem cell22_910844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_910844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_910844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_910844 prefixEnd_910844 := by exact prefixLift 910844
  have htrace : WordTrace (prefixWord ++ tailWord_910844) baseStart_910844 baseEnd_910844 := by
    simpa [prefixWord, tailWord_910844, baseEnd_910844] using wordTrace_append hprefix tailTrace_910844
  have hstable : (prefixWord ++ tailWord_910844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910844).length < 2 ^ (prefixWord ++ tailWord_910844).sum := by decide
  have hdescent : baseEnd_910844 < baseStart_910844 := by decide
  rcases family_descends (prefixWord ++ tailWord_910844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910857 : List Nat := [1, 2, 1, 1, 3, 1, 13]
def baseStart_910857 : Nat := 118140960795 + 910857 * 2 ^ 59
def prefixEnd_910857 : Nat := 4983230072969 + 3 ^ 40 * 910857 * 2
def baseEnd_910857 : Nat := 11548332062035753123421

theorem tailTrace_910857 : CollatzResearch.WordTrace tailWord_910857 prefixEnd_910857 11548332062035753123421 := by
  unfold tailWord_910857
  simp only [CollatzResearch.WordTrace]
  refine ⟨33221684061128125835786825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22147789374085417223857883 33221684061128125835786825)
  ·
    refine ⟨24916263045846094376840119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33221684061128125835786825 24916263045846094376840119)
    ·
      refine ⟨37374394568769141565260179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24916263045846094376840119 37374394568769141565260179)
      ·
        refine ⟨56061591853153712347890269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37374394568769141565260179 56061591853153712347890269)
        ·
          refine ⟨21023096944932642130458851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56061591853153712347890269 21023096944932642130458851)
          ·
            refine ⟨31534645417398963195688277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21023096944932642130458851 31534645417398963195688277)
            ·
              refine ⟨11548332062035753123421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 31534645417398963195688277 11548332062035753123421)
              ·
                rfl

theorem cell22_910857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 13].length) (baseStart_910857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_910857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_910857 prefixEnd_910857 := by exact prefixLift 910857
  have htrace : WordTrace (prefixWord ++ tailWord_910857) baseStart_910857 baseEnd_910857 := by
    simpa [prefixWord, tailWord_910857, baseEnd_910857] using wordTrace_append hprefix tailTrace_910857
  have hstable : (prefixWord ++ tailWord_910857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910857).length < 2 ^ (prefixWord ++ tailWord_910857).sum := by decide
  have hdescent : baseEnd_910857 < baseStart_910857 := by decide
  rcases family_descends (prefixWord ++ tailWord_910857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910979 : List Nat := [1, 1, 1, 3, 3, 1, 1, 1, 5, 5]
def baseStart_910979 : Nat := 118140960795 + 910979 * 2 ^ 59
def prefixEnd_910979 : Nat := 4983230072969 + 3 ^ 40 * 910979 * 2
def baseEnd_910979 : Nat := 311846728768197682781993

theorem tailTrace_910979 : CollatzResearch.WordTrace tailWord_910979 prefixEnd_910979 311846728768197682781993 := by
  unfold tailWord_910979
  simp only [CollatzResearch.WordTrace]
  refine ⟨33226133766686140671727991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22150755844457427114485327 33226133766686140671727991)
  ·
    refine ⟨49839200650029211007591987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33226133766686140671727991 49839200650029211007591987)
    ·
      refine ⟨74758800975043816511387981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49839200650029211007591987 74758800975043816511387981)
      ·
        refine ⟨28034550365641431191770493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74758800975043816511387981 28034550365641431191770493)
        ·
          refine ⟨10512956387115536696913935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28034550365641431191770493 10512956387115536696913935)
          ·
            refine ⟨15769434580673305045370903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10512956387115536696913935 15769434580673305045370903)
            ·
              refine ⟨23654151871009957568056355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15769434580673305045370903 23654151871009957568056355)
              ·
                refine ⟨35481227806514936352084533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23654151871009957568056355 35481227806514936352084533)
                ·
                  refine ⟨3326365106860775283007925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35481227806514936352084533 3326365106860775283007925)
                  ·
                    refine ⟨311846728768197682781993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3326365106860775283007925 311846728768197682781993)
                    ·
                      rfl

theorem cell22_910979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5, 5].length) (baseStart_910979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_910979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_910979 prefixEnd_910979 := by exact prefixLift 910979
  have htrace : WordTrace (prefixWord ++ tailWord_910979) baseStart_910979 baseEnd_910979 := by
    simpa [prefixWord, tailWord_910979, baseEnd_910979] using wordTrace_append hprefix tailTrace_910979
  have hstable : (prefixWord ++ tailWord_910979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910979).length < 2 ^ (prefixWord ++ tailWord_910979).sum := by decide
  have hdescent : baseEnd_910979 < baseStart_910979 := by decide
  rcases family_descends (prefixWord ++ tailWord_910979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911060 : List Nat := [2, 4, 1, 3, 1, 3, 2, 6]
def baseStart_911060 : Nat := 118140960795 + 911060 * 2 ^ 59
def prefixEnd_911060 : Nat := 4983230072969 + 3 ^ 40 * 911060 * 2
def baseEnd_911060 : Nat := 34652717413726719056305

theorem tailTrace_911060 : CollatzResearch.WordTrace tailWord_911060 prefixEnd_911060 34652717413726719056305 := by
  unfold tailWord_911060
  simp only [CollatzResearch.WordTrace]
  refine ⟨16614544039696345752713317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22152725386261794336951089 16614544039696345752713317)
  ·
    refine ⟨3115227007443064828633747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16614544039696345752713317 3115227007443064828633747)
    ·
      refine ⟨4672840511164597242950621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3115227007443064828633747 4672840511164597242950621)
      ·
        refine ⟨1752315191686723966106483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4672840511164597242950621 1752315191686723966106483)
        ·
          refine ⟨2628472787530085949159725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1752315191686723966106483 2628472787530085949159725)
          ·
            refine ⟨985677295323782230934897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2628472787530085949159725 985677295323782230934897)
            ·
              refine ⟨739257971492836673201173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 985677295323782230934897 739257971492836673201173)
              ·
                refine ⟨34652717413726719056305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 739257971492836673201173 34652717413726719056305)
                ·
                  rfl

theorem cell22_911060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 6].length) (baseStart_911060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_911060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_911060 prefixEnd_911060 := by exact prefixLift 911060
  have htrace : WordTrace (prefixWord ++ tailWord_911060) baseStart_911060 baseEnd_911060 := by
    simpa [prefixWord, tailWord_911060, baseEnd_911060] using wordTrace_append hprefix tailTrace_911060
  have hstable : (prefixWord ++ tailWord_911060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911060).length < 2 ^ (prefixWord ++ tailWord_911060).sum := by decide
  have hdescent : baseEnd_911060 < baseStart_911060 := by decide
  rcases family_descends (prefixWord ++ tailWord_911060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911116 : List Nat := [2, 2, 1, 2, 2, 1, 2, 4, 6]
def baseStart_911116 : Nat := 118140960795 + 911116 * 2 ^ 59
def prefixEnd_911116 : Nat := 4983230072969 + 3 ^ 40 * 911116 * 2
def baseEnd_911116 : Nat := 103964542222658330702191

theorem tailTrace_911116 : CollatzResearch.WordTrace tailWord_911116 prefixEnd_911116 103964542222658330702191 := by
  unfold tailWord_911116
  simp only [CollatzResearch.WordTrace]
  refine ⟨16615565283594906534732601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22154087044793208712976801 16615565283594906534732601)
  ·
    refine ⟨12461673962696179901049451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16615565283594906534732601 12461673962696179901049451)
    ·
      refine ⟨18692510944044269851574177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12461673962696179901049451 18692510944044269851574177)
      ·
        refine ⟨14019383208033202388680633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18692510944044269851574177 14019383208033202388680633)
        ·
          refine ⟨10514537406024901791510475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14019383208033202388680633 10514537406024901791510475)
          ·
            refine ⟨15771806109037352687265713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10514537406024901791510475 15771806109037352687265713)
            ·
              refine ⟨11828854581778014515449285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15771806109037352687265713 11828854581778014515449285)
              ·
                refine ⟨2217910234083377721646741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11828854581778014515449285 2217910234083377721646741)
                ·
                  refine ⟨103964542222658330702191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2217910234083377721646741 103964542222658330702191)
                  ·
                    rfl

theorem cell22_911116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4, 6].length) (baseStart_911116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_911116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_911116 prefixEnd_911116 := by exact prefixLift 911116
  have htrace : WordTrace (prefixWord ++ tailWord_911116) baseStart_911116 baseEnd_911116 := by
    simpa [prefixWord, tailWord_911116, baseEnd_911116] using wordTrace_append hprefix tailTrace_911116
  have hstable : (prefixWord ++ tailWord_911116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911116).length < 2 ^ (prefixWord ++ tailWord_911116).sum := by decide
  have hdescent : baseEnd_911116 < baseStart_911116 := by decide
  rcases family_descends (prefixWord ++ tailWord_911116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911131 : List Nat := [1, 1, 1, 1, 1, 1, 4, 6, 1, 5]
def baseStart_911131 : Nat := 118140960795 + 911131 * 2 ^ 59
def prefixEnd_911131 : Nat := 4983230072969 + 3 ^ 40 * 911131 * 2
def baseEnd_911131 : Nat := 311898761474519952981527

theorem tailTrace_911131 : CollatzResearch.WordTrace tailWord_911131 prefixEnd_911131 311898761474519952981527 := by
  unfold tailWord_911131
  simp only [CollatzResearch.WordTrace]
  refine ⟨33231677662135470631261247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22154451774756980420840831 33231677662135470631261247)
  ·
    refine ⟨49847516493203205946891871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33231677662135470631261247 49847516493203205946891871)
    ·
      refine ⟨74771274739804808920337807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49847516493203205946891871 74771274739804808920337807)
      ·
        refine ⟨112156912109707213380506711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74771274739804808920337807 112156912109707213380506711)
        ·
          refine ⟨168235368164560820070760067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112156912109707213380506711 168235368164560820070760067)
          ·
            refine ⟨252353052246841230106140101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168235368164560820070760067 252353052246841230106140101)
            ·
              refine ⟨47316197296282730644901269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 252353052246841230106140101 47316197296282730644901269)
              ·
                refine ⟨2217946748263252998979747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47316197296282730644901269 2217946748263252998979747)
                ·
                  refine ⟨3326920122394879498469621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2217946748263252998979747 3326920122394879498469621)
                  ·
                    refine ⟨311898761474519952981527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3326920122394879498469621 311898761474519952981527)
                    ·
                      rfl

theorem cell22_911131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 1, 5].length) (baseStart_911131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_911131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_911131 prefixEnd_911131 := by exact prefixLift 911131
  have htrace : WordTrace (prefixWord ++ tailWord_911131) baseStart_911131 baseEnd_911131 := by
    simpa [prefixWord, tailWord_911131, baseEnd_911131] using wordTrace_append hprefix tailTrace_911131
  have hstable : (prefixWord ++ tailWord_911131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911131).length < 2 ^ (prefixWord ++ tailWord_911131).sum := by decide
  have hdescent : baseEnd_911131 < baseStart_911131 := by decide
  rcases family_descends (prefixWord ++ tailWord_911131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911135 : List Nat := [1, 1, 2, 4, 2, 1, 5, 1, 1, 4]
def baseStart_911135 : Nat := 118140960795 + 911135 * 2 ^ 59
def prefixEnd_911135 : Nat := 4983230072969 + 3 ^ 40 * 911135 * 2
def baseEnd_911135 : Nat := 311900130756265275881515

theorem tailTrace_911135 : CollatzResearch.WordTrace tailWord_911135 prefixEnd_911135 311900130756265275881515 := by
  unfold tailWord_911135
  simp only [CollatzResearch.WordTrace]
  refine ⟨33231823554120979314406859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22154549036080652876271239 33231823554120979314406859)
  ·
    refine ⟨49847735331181468971610289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33231823554120979314406859 49847735331181468971610289)
    ·
      refine ⟨37385801498386101728707717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49847735331181468971610289 37385801498386101728707717)
      ·
        refine ⟨7009837780947394074132697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37385801498386101728707717 7009837780947394074132697)
        ·
          refine ⟨5257378335710545555599523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7009837780947394074132697 5257378335710545555599523)
          ·
            refine ⟨7886067503565818333399285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5257378335710545555599523 7886067503565818333399285)
            ·
              refine ⟨739318828459295468756183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7886067503565818333399285 739318828459295468756183)
              ·
                refine ⟨1108978242688943203134275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 739318828459295468756183 1108978242688943203134275)
                ·
                  refine ⟨1663467364033414804701413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1108978242688943203134275 1663467364033414804701413)
                  ·
                    refine ⟨311900130756265275881515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1663467364033414804701413 311900130756265275881515)
                    ·
                      rfl

theorem cell22_911135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 1, 1, 4].length) (baseStart_911135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_911135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_911135 prefixEnd_911135 := by exact prefixLift 911135
  have htrace : WordTrace (prefixWord ++ tailWord_911135) baseStart_911135 baseEnd_911135 := by
    simpa [prefixWord, tailWord_911135, baseEnd_911135] using wordTrace_append hprefix tailTrace_911135
  have hstable : (prefixWord ++ tailWord_911135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911135).length < 2 ^ (prefixWord ++ tailWord_911135).sum := by decide
  have hdescent : baseEnd_911135 < baseStart_911135 := by decide
  rcases family_descends (prefixWord ++ tailWord_911135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911165 : List Nat := [1, 4, 1, 4, 1, 2, 2, 1, 1, 5]
def baseStart_911165 : Nat := 118140960795 + 911165 * 2 ^ 59
def prefixEnd_911165 : Nat := 4983230072969 + 3 ^ 40 * 911165 * 2
def baseEnd_911165 : Nat := 311910400369355197631423

theorem tailTrace_911165 : CollatzResearch.WordTrace tailWord_911165 prefixEnd_911165 311910400369355197631423 := by
  unfold tailWord_911165
  simp only [CollatzResearch.WordTrace]
  refine ⟨33232917744012294437998949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22155278496008196291999299 33232917744012294437998949)
  ·
    refine ⟨6231172077002305207124803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33232917744012294437998949 6231172077002305207124803)
    ·
      refine ⟨9346758115503457810687205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6231172077002305207124803 9346758115503457810687205)
      ·
        refine ⟨1752517146656898339503851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9346758115503457810687205 1752517146656898339503851)
        ·
          refine ⟨2628775719985347509255777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1752517146656898339503851 2628775719985347509255777)
          ·
            refine ⟨1971581789989010631941833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2628775719985347509255777 1971581789989010631941833)
            ·
              refine ⟨1478686342491757973956375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1971581789989010631941833 1478686342491757973956375)
              ·
                refine ⟨2218029513737636960934563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1478686342491757973956375 2218029513737636960934563)
                ·
                  refine ⟨3327044270606455441401845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2218029513737636960934563 3327044270606455441401845)
                  ·
                    refine ⟨311910400369355197631423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3327044270606455441401845 311910400369355197631423)
                    ·
                      rfl

theorem cell22_911165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 1, 1, 5].length) (baseStart_911165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_911165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_911165 prefixEnd_911165 := by exact prefixLift 911165
  have htrace : WordTrace (prefixWord ++ tailWord_911165) baseStart_911165 baseEnd_911165 := by
    simpa [prefixWord, tailWord_911165, baseEnd_911165] using wordTrace_append hprefix tailTrace_911165
  have hstable : (prefixWord ++ tailWord_911165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911165).length < 2 ^ (prefixWord ++ tailWord_911165).sum := by decide
  have hdescent : baseEnd_911165 < baseStart_911165 := by decide
  rcases family_descends (prefixWord ++ tailWord_911165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911178 : List Nat := [3, 1, 2, 1, 1, 1, 7, 6]
def baseStart_911178 : Nat := 118140960795 + 911178 * 2 ^ 59
def prefixEnd_911178 : Nat := 4983230072969 + 3 ^ 40 * 911178 * 2
def baseEnd_911178 : Nat := 34657205615003055228487

theorem tailTrace_911178 : CollatzResearch.WordTrace tailWord_911178 prefixEnd_911178 34657205615003055228487 := by
  unfold tailWord_911178
  simp only [CollatzResearch.WordTrace]
  refine ⟨8308347973241299414555547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22155594595310131772148125 8308347973241299414555547)
  ·
    refine ⟨12462521959861949121833321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8308347973241299414555547 12462521959861949121833321)
    ·
      refine ⟨9346891469896461841374991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12462521959861949121833321 9346891469896461841374991)
      ·
        refine ⟨14020337204844692762062487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9346891469896461841374991 14020337204844692762062487)
        ·
          refine ⟨21030505807267039143093731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14020337204844692762062487 21030505807267039143093731)
          ·
            refine ⟨31545758710900558714640597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21030505807267039143093731 31545758710900558714640597)
            ·
              refine ⟨739353719786731844874389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 31545758710900558714640597 739353719786731844874389)
              ·
                refine ⟨34657205615003055228487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 739353719786731844874389 34657205615003055228487)
                ·
                  rfl

theorem cell22_911178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 6].length) (baseStart_911178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_911178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_911178 prefixEnd_911178 := by exact prefixLift 911178
  have htrace : WordTrace (prefixWord ++ tailWord_911178) baseStart_911178 baseEnd_911178 := by
    simpa [prefixWord, tailWord_911178, baseEnd_911178] using wordTrace_append hprefix tailTrace_911178
  have hstable : (prefixWord ++ tailWord_911178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911178).length < 2 ^ (prefixWord ++ tailWord_911178).sum := by decide
  have hdescent : baseEnd_911178 < baseStart_911178 := by decide
  rcases family_descends (prefixWord ++ tailWord_911178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911193 : List Nat := [1, 2, 1, 2, 2, 3, 1, 2, 5, 3]
def baseStart_911193 : Nat := 118140960795 + 911193 * 2 ^ 59
def prefixEnd_911193 : Nat := 4983230072969 + 3 ^ 40 * 911193 * 2
def baseEnd_911193 : Nat := 311919985341572457931337

theorem tailTrace_911193 : CollatzResearch.WordTrace tailWord_911193 prefixEnd_911193 311919985341572457931337 := by
  unfold tailWord_911193
  simp only [CollatzResearch.WordTrace]
  refine ⟨33233938987910855220018233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22155959325273903480012155 33233938987910855220018233)
  ·
    refine ⟨24925454240933141415013675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33233938987910855220018233 24925454240933141415013675)
    ·
      refine ⟨37388181361399712122520513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24925454240933141415013675 37388181361399712122520513)
      ·
        refine ⟨28041136021049784091890385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37388181361399712122520513 28041136021049784091890385)
        ·
          refine ⟨21030852015787338068917789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28041136021049784091890385 21030852015787338068917789)
          ·
            refine ⟨7886569505920251775844171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21030852015787338068917789 7886569505920251775844171)
            ·
              refine ⟨11829854258880377663766257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7886569505920251775844171 11829854258880377663766257)
              ·
                refine ⟨8872390694160283247824693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11829854258880377663766257 8872390694160283247824693)
                ·
                  refine ⟨831786627577526554483565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8872390694160283247824693 831786627577526554483565)
                  ·
                    refine ⟨311919985341572457931337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 831786627577526554483565 311919985341572457931337)
                    ·
                      rfl

theorem cell22_911193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 5, 3].length) (baseStart_911193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_911193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_911193 prefixEnd_911193 := by exact prefixLift 911193
  have htrace : WordTrace (prefixWord ++ tailWord_911193) baseStart_911193 baseEnd_911193 := by
    simpa [prefixWord, tailWord_911193, baseEnd_911193] using wordTrace_append hprefix tailTrace_911193
  have hstable : (prefixWord ++ tailWord_911193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911193).length < 2 ^ (prefixWord ++ tailWord_911193).sum := by decide
  have hdescent : baseEnd_911193 < baseStart_911193 := by decide
  rcases family_descends (prefixWord ++ tailWord_911193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911283 : List Nat := [1, 1, 1, 2, 3, 1, 4, 3, 1, 5]
def baseStart_911283 : Nat := 118140960795 + 911283 * 2 ^ 59
def prefixEnd_911283 : Nat := 4983230072969 + 3 ^ 40 * 911283 * 2
def baseEnd_911283 : Nat := 311950794180842223181061

theorem tailTrace_911283 : CollatzResearch.WordTrace tailWord_911283 prefixEnd_911283 311950794180842223181061 := by
  unfold tailWord_911283
  simp only [CollatzResearch.WordTrace]
  refine ⟨33237221557584800590794503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22158147705056533727196335 33237221557584800590794503)
  ·
    refine ⟨49855832336377200886191755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33237221557584800590794503 49855832336377200886191755)
    ·
      refine ⟨74783748504565801329287633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49855832336377200886191755 74783748504565801329287633)
      ·
        refine ⟨56087811378424350996965725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74783748504565801329287633 56087811378424350996965725)
        ·
          refine ⟨21032929266909131623862147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56087811378424350996965725 21032929266909131623862147)
          ·
            refine ⟨31549393900363697435793221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21032929266909131623862147 31549393900363697435793221)
            ·
              refine ⟨5915511356318193269211229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31549393900363697435793221 5915511356318193269211229)
              ·
                refine ⟨2218316758619322475954211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5915511356318193269211229 2218316758619322475954211)
                ·
                  refine ⟨3327475137928983713931317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2218316758619322475954211 3327475137928983713931317)
                  ·
                    refine ⟨311950794180842223181061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3327475137928983713931317 311950794180842223181061)
                    ·
                      rfl

theorem cell22_911283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3, 1, 5].length) (baseStart_911283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_911283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_911283 prefixEnd_911283 := by exact prefixLift 911283
  have htrace : WordTrace (prefixWord ++ tailWord_911283) baseStart_911283 baseEnd_911283 := by
    simpa [prefixWord, tailWord_911283, baseEnd_911283] using wordTrace_append hprefix tailTrace_911283
  have hstable : (prefixWord ++ tailWord_911283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911283).length < 2 ^ (prefixWord ++ tailWord_911283).sum := by decide
  have hdescent : baseEnd_911283 < baseStart_911283 := by decide
  rcases family_descends (prefixWord ++ tailWord_911283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911317 : List Nat := [1, 3, 2, 3, 2, 1, 1, 4, 2, 3]
def baseStart_911317 : Nat := 118140960795 + 911317 * 2 ^ 59
def prefixEnd_911317 : Nat := 4983230072969 + 3 ^ 40 * 911317 * 2
def baseEnd_911317 : Nat := 311962433075677467830957

theorem tailTrace_911317 : CollatzResearch.WordTrace tailWord_911317 prefixEnd_911317 311962433075677467830957 := by
  unfold tailWord_911317
  simp only [CollatzResearch.WordTrace]
  refine ⟨33238461639461624397532205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22158974426307749598354803 33238461639461624397532205)
  ·
    refine ⟨12464423114798109149074577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33238461639461624397532205 12464423114798109149074577)
    ·
      refine ⟨9348317336098581861805933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12464423114798109149074577 9348317336098581861805933)
      ·
        refine ⟨3505619001036968198177225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9348317336098581861805933 3505619001036968198177225)
        ·
          refine ⟨2629214250777726148632919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3505619001036968198177225 2629214250777726148632919)
          ·
            refine ⟨3943821376166589222949379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2629214250777726148632919 3943821376166589222949379)
            ·
              refine ⟨5915732064249883834424069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3943821376166589222949379 5915732064249883834424069)
              ·
                refine ⟨1109199762046853218954513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5915732064249883834424069 1109199762046853218954513)
                ·
                  refine ⟨831899821535139914215885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1109199762046853218954513 831899821535139914215885)
                  ·
                    refine ⟨311962433075677467830957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 831899821535139914215885 311962433075677467830957)
                    ·
                      rfl

theorem cell22_911317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 4, 2, 3].length) (baseStart_911317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_911317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_911317 prefixEnd_911317 := by exact prefixLift 911317
  have htrace : WordTrace (prefixWord ++ tailWord_911317) baseStart_911317 baseEnd_911317 := by
    simpa [prefixWord, tailWord_911317, baseEnd_911317] using wordTrace_append hprefix tailTrace_911317
  have hstable : (prefixWord ++ tailWord_911317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911317).length < 2 ^ (prefixWord ++ tailWord_911317).sum := by decide
  have hdescent : baseEnd_911317 < baseStart_911317 := by decide
  rcases family_descends (prefixWord ++ tailWord_911317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911343 : List Nat := [1, 1, 2, 1, 4, 2, 1, 2, 2, 6]
def baseStart_911343 : Nat := 118140960795 + 911343 * 2 ^ 59
def prefixEnd_911343 : Nat := 4983230072969 + 3 ^ 40 * 911343 * 2
def baseEnd_911343 : Nat := 311971333407022066680877

theorem tailTrace_911343 : CollatzResearch.WordTrace tailWord_911343 prefixEnd_911343 311971333407022066680877 := by
  unfold tailWord_911343
  simp only [CollatzResearch.WordTrace]
  refine ⟨33239409937367430837978683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22159606624911620558652455 33239409937367430837978683)
  ·
    refine ⟨49859114906051146256968025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33239409937367430837978683 49859114906051146256968025)
    ·
      refine ⟨37394336179538359692726019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49859114906051146256968025 37394336179538359692726019)
      ·
        refine ⟨56091504269307539539089029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37394336179538359692726019 56091504269307539539089029)
        ·
          refine ⟨10517157050495163663579193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56091504269307539539089029 10517157050495163663579193)
          ·
            refine ⟨7887867787871372747684395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10517157050495163663579193 7887867787871372747684395)
            ·
              refine ⟨11831801681807059121526593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7887867787871372747684395 11831801681807059121526593)
              ·
                refine ⟨8873851261355294341144945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11831801681807059121526593 8873851261355294341144945)
                ·
                  refine ⟨6655388446016470755858709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8873851261355294341144945 6655388446016470755858709)
                  ·
                    refine ⟨311971333407022066680877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6655388446016470755858709 311971333407022066680877)
                    ·
                      rfl

theorem cell22_911343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 6].length) (baseStart_911343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_911343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_911343 prefixEnd_911343 := by exact prefixLift 911343
  have htrace : WordTrace (prefixWord ++ tailWord_911343) baseStart_911343 baseEnd_911343 := by
    simpa [prefixWord, tailWord_911343, baseEnd_911343] using wordTrace_append hprefix tailTrace_911343
  have hstable : (prefixWord ++ tailWord_911343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911343).length < 2 ^ (prefixWord ++ tailWord_911343).sum := by decide
  have hdescent : baseEnd_911343 < baseStart_911343 := by decide
  rcases family_descends (prefixWord ++ tailWord_911343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911403 : List Nat := [1, 1, 1, 1, 2, 1, 4, 3, 8]
def baseStart_911403 : Nat := 118140960795 + 911403 * 2 ^ 59
def prefixEnd_911403 : Nat := 4983230072969 + 3 ^ 40 * 911403 * 2
def baseEnd_911403 : Nat := 103997290877733970060231

theorem tailTrace_911403 : CollatzResearch.WordTrace tailWord_911403 prefixEnd_911403 103997290877733970060231 := by
  unfold tailWord_911403
  simp only [CollatzResearch.WordTrace]
  refine ⟨33241598317150061085162863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22161065544766707390108575 33241598317150061085162863)
  ·
    refine ⟨49862397475725091627744295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33241598317150061085162863 49862397475725091627744295)
    ·
      refine ⟨74793596213587637441616443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49862397475725091627744295 74793596213587637441616443)
      ·
        refine ⟨112190394320381456162424665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74793596213587637441616443 112190394320381456162424665)
        ·
          refine ⟨84142795740286092121818499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112190394320381456162424665 84142795740286092121818499)
          ·
            refine ⟨126214193610429138182727749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84142795740286092121818499 126214193610429138182727749)
            ·
              refine ⟨23665161301955463409261453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126214193610429138182727749 23665161301955463409261453)
              ·
                refine ⟨8874435488233298778473045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23665161301955463409261453 8874435488233298778473045)
                ·
                  refine ⟨103997290877733970060231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8874435488233298778473045 103997290877733970060231)
                  ·
                    rfl

theorem cell22_911403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 8].length) (baseStart_911403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_911403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_911403 prefixEnd_911403 := by exact prefixLift 911403
  have htrace : WordTrace (prefixWord ++ tailWord_911403) baseStart_911403 baseEnd_911403 := by
    simpa [prefixWord, tailWord_911403, baseEnd_911403] using wordTrace_append hprefix tailTrace_911403
  have hstable : (prefixWord ++ tailWord_911403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911403).length < 2 ^ (prefixWord ++ tailWord_911403).sum := by decide
  have hdescent : baseEnd_911403 < baseStart_911403 := by decide
  rcases family_descends (prefixWord ++ tailWord_911403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911450 : List Nat := [3, 1, 1, 2, 1, 1, 3, 2, 4, 4]
def baseStart_911450 : Nat := 118140960795 + 911450 * 2 ^ 59
def prefixEnd_911450 : Nat := 4983230072969 + 3 ^ 40 * 911450 * 2
def baseEnd_911450 : Nat := 312007961693709454255549

theorem tailTrace_911450 : CollatzResearch.WordTrace tailWord_911450 prefixEnd_911450 312007961693709454255549 := by
  unfold tailWord_911450
  simp only [CollatzResearch.WordTrace]
  refine ⟨8310828136994947028030951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22162208365319858741415869 8310828136994947028030951)
  ·
    refine ⟨12466242205492420542046427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8310828136994947028030951 12466242205492420542046427)
    ·
      refine ⟨18699363308238630813069641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12466242205492420542046427 18699363308238630813069641)
      ·
        refine ⟨14024522481178973109802231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18699363308238630813069641 14024522481178973109802231)
        ·
          refine ⟨21036783721768459664703347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14024522481178973109802231 21036783721768459664703347)
          ·
            refine ⟨31555175582652689497055021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21036783721768459664703347 31555175582652689497055021)
            ·
              refine ⟨11833190843494758561395633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31555175582652689497055021 11833190843494758561395633)
              ·
                refine ⟨8874893132621068921046725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11833190843494758561395633 8874893132621068921046725)
                ·
                  refine ⟨1664042462366450422696261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8874893132621068921046725 1664042462366450422696261)
                  ·
                    refine ⟨312007961693709454255549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1664042462366450422696261 312007961693709454255549)
                    ·
                      rfl

theorem cell22_911450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 4, 4].length) (baseStart_911450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_911450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_911450 prefixEnd_911450 := by exact prefixLift 911450
  have htrace : WordTrace (prefixWord ++ tailWord_911450) baseStart_911450 baseEnd_911450 := by
    simpa [prefixWord, tailWord_911450, baseEnd_911450] using wordTrace_append hprefix tailTrace_911450
  have hstable : (prefixWord ++ tailWord_911450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911450).length < 2 ^ (prefixWord ++ tailWord_911450).sum := by decide
  have hdescent : baseEnd_911450 < baseStart_911450 := by decide
  rcases family_descends (prefixWord ++ tailWord_911450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911495 : List Nat := [1, 1, 4, 2, 1, 1, 3, 1, 2, 6]
def baseStart_911495 : Nat := 118140960795 + 911495 * 2 ^ 59
def prefixEnd_911495 : Nat := 4983230072969 + 3 ^ 40 * 911495 * 2
def baseEnd_911495 : Nat := 312023366113344336880411

theorem tailTrace_911495 : CollatzResearch.WordTrace tailWord_911495 prefixEnd_911495 312023366113344336880411 := by
  unfold tailWord_911495
  simp only [CollatzResearch.WordTrace]
  refine ⟨33244953832816760797511939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22163302555211173865007959 33244953832816760797511939)
  ·
    refine ⟨49867430749225141196267909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33244953832816760797511939 49867430749225141196267909)
    ·
      refine ⟨9350143265479713974300233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49867430749225141196267909 9350143265479713974300233)
      ·
        refine ⟨7012607449109785480725175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9350143265479713974300233 7012607449109785480725175)
        ·
          refine ⟨10518911173664678221087763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7012607449109785480725175 10518911173664678221087763)
          ·
            refine ⟨15778366760497017331631645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10518911173664678221087763 15778366760497017331631645)
            ·
              refine ⟨5916887535186381499361867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15778366760497017331631645 5916887535186381499361867)
              ·
                refine ⟨8875331302779572249042801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5916887535186381499361867 8875331302779572249042801)
                ·
                  refine ⟨6656498477084679186782101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8875331302779572249042801 6656498477084679186782101)
                  ·
                    refine ⟨312023366113344336880411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6656498477084679186782101 312023366113344336880411)
                    ·
                      rfl

theorem cell22_911495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_911495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_911495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_911495 prefixEnd_911495 := by exact prefixLift 911495
  have htrace : WordTrace (prefixWord ++ tailWord_911495) baseStart_911495 baseEnd_911495 := by
    simpa [prefixWord, tailWord_911495, baseEnd_911495] using wordTrace_append hprefix tailTrace_911495
  have hstable : (prefixWord ++ tailWord_911495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911495).length < 2 ^ (prefixWord ++ tailWord_911495).sum := by decide
  have hdescent : baseEnd_911495 < baseStart_911495 := by decide
  rcases family_descends (prefixWord ++ tailWord_911495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911497 : List Nat := [1, 2, 1, 1, 4, 2, 2, 3, 3, 3]
def baseStart_911497 : Nat := 118140960795 + 911497 * 2 ^ 59
def prefixEnd_911497 : Nat := 4983230072969 + 3 ^ 40 * 911497 * 2
def baseEnd_911497 : Nat := 312024050754216998330405

theorem tailTrace_911497 : CollatzResearch.WordTrace tailWord_911497 prefixEnd_911497 312024050754216998330405 := by
  unfold tailWord_911497
  simp only [CollatzResearch.WordTrace]
  refine ⟨33245026778809515139084745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22163351185873010092723163 33245026778809515139084745)
  ·
    refine ⟨24933770084107136354313559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33245026778809515139084745 24933770084107136354313559)
    ·
      refine ⟨37400655126160704531470339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24933770084107136354313559 37400655126160704531470339)
      ·
        refine ⟨56100982689241056797205509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37400655126160704531470339 56100982689241056797205509)
        ·
          refine ⟨10518934254232698149476033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56100982689241056797205509 10518934254232698149476033)
          ·
            refine ⟨7889200690674523612107025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10518934254232698149476033 7889200690674523612107025)
            ·
              refine ⟨5916900518005892709080269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7889200690674523612107025 5916900518005892709080269)
              ·
                refine ⟨2218837694252209765905101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5916900518005892709080269 2218837694252209765905101)
                ·
                  refine ⟨832064135344578662214413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2218837694252209765905101 832064135344578662214413)
                  ·
                    refine ⟨312024050754216998330405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 832064135344578662214413 312024050754216998330405)
                    ·
                      rfl

theorem cell22_911497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3, 3, 3].length) (baseStart_911497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_911497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_911497 prefixEnd_911497 := by exact prefixLift 911497
  have htrace : WordTrace (prefixWord ++ tailWord_911497) baseStart_911497 baseEnd_911497 := by
    simpa [prefixWord, tailWord_911497, baseEnd_911497] using wordTrace_append hprefix tailTrace_911497
  have hstable : (prefixWord ++ tailWord_911497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911497).length < 2 ^ (prefixWord ++ tailWord_911497).sum := by decide
  have hdescent : baseEnd_911497 < baseStart_911497 := by decide
  rcases family_descends (prefixWord ++ tailWord_911497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911518 : List Nat := [4, 3, 1, 1, 4, 1, 1, 1, 2, 4]
def baseStart_911518 : Nat := 118140960795 + 911518 * 2 ^ 59
def prefixEnd_911518 : Nat := 4983230072969 + 3 ^ 40 * 911518 * 2
def baseEnd_911518 : Nat := 312031239483379943555341

theorem tailTrace_911518 : CollatzResearch.WordTrace tailWord_911518 prefixEnd_911518 312031239483379943555341 := by
  unfold tailWord_911518
  simp only [CollatzResearch.WordTrace]
  refine ⟨4155724088966679465699901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22163861807822290483732805 4155724088966679465699901)
  ·
    refine ⟨1558396533362504799637463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4155724088966679465699901 1558396533362504799637463)
    ·
      refine ⟨2337594800043757199456195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1558396533362504799637463 2337594800043757199456195)
      ·
        refine ⟨3506392200065635799184293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2337594800043757199456195 3506392200065635799184293)
        ·
          refine ⟨657448537512306712347055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3506392200065635799184293 657448537512306712347055)
          ·
            refine ⟨986172806268460068520583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 657448537512306712347055 986172806268460068520583)
            ·
              refine ⟨1479259209402690102780875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 986172806268460068520583 1479259209402690102780875)
              ·
                refine ⟨2218888814104035154171313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1479259209402690102780875 2218888814104035154171313)
                ·
                  refine ⟨1664166610578026365628485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2218888814104035154171313 1664166610578026365628485)
                  ·
                    refine ⟨312031239483379943555341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1664166610578026365628485 312031239483379943555341)
                    ·
                      rfl

theorem cell22_911518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_911518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_911518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_911518 prefixEnd_911518 := by exact prefixLift 911518
  have htrace : WordTrace (prefixWord ++ tailWord_911518) baseStart_911518 baseEnd_911518 := by
    simpa [prefixWord, tailWord_911518, baseEnd_911518] using wordTrace_append hprefix tailTrace_911518
  have hstable : (prefixWord ++ tailWord_911518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911518).length < 2 ^ (prefixWord ++ tailWord_911518).sum := by decide
  have hdescent : baseEnd_911518 < baseStart_911518 := by decide
  rcases family_descends (prefixWord ++ tailWord_911518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911525 : List Nat := [1, 3, 1, 2, 1, 3, 1, 2, 1, 7]
def baseStart_911525 : Nat := 118140960795 + 911525 * 2 ^ 59
def prefixEnd_911525 : Nat := 4983230072969 + 3 ^ 40 * 911525 * 2
def baseEnd_911525 : Nat := 312033635726434258630319

theorem tailTrace_911525 : CollatzResearch.WordTrace tailWord_911525 prefixEnd_911525 312033635726434258630319 := by
  unfold tailWord_911525
  simp only [CollatzResearch.WordTrace]
  refine ⟨33246048022708075921104029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22164032015138717280736019 33246048022708075921104029)
  ·
    refine ⟨12467268008515528470414011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33246048022708075921104029 12467268008515528470414011)
    ·
      refine ⟨18700902012773292705621017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12467268008515528470414011 18700902012773292705621017)
      ·
        refine ⟨14025676509579969529215763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18700902012773292705621017 14025676509579969529215763)
        ·
          refine ⟨21038514764369954293823645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14025676509579969529215763 21038514764369954293823645)
          ·
            refine ⟨7889443036638732860183867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21038514764369954293823645 7889443036638732860183867)
            ·
              refine ⟨11834164554958099290275801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7889443036638732860183867 11834164554958099290275801)
              ·
                refine ⟨8875623416218574467706851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11834164554958099290275801 8875623416218574467706851)
                ·
                  refine ⟨13313435124327861701560277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8875623416218574467706851 13313435124327861701560277)
                  ·
                    refine ⟨312033635726434258630319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13313435124327861701560277 312033635726434258630319)
                    ·
                      rfl

theorem cell22_911525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 7].length) (baseStart_911525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_911525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_911525 prefixEnd_911525 := by exact prefixLift 911525
  have htrace : WordTrace (prefixWord ++ tailWord_911525) baseStart_911525 baseEnd_911525 := by
    simpa [prefixWord, tailWord_911525, baseEnd_911525] using wordTrace_append hprefix tailTrace_911525
  have hstable : (prefixWord ++ tailWord_911525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911525).length < 2 ^ (prefixWord ++ tailWord_911525).sum := by decide
  have hdescent : baseEnd_911525 < baseStart_911525 := by decide
  rcases family_descends (prefixWord ++ tailWord_911525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911617 : List Nat := [1, 2, 4, 1, 1, 2, 4, 7]
def baseStart_911617 : Nat := 118140960795 + 911617 * 2 ^ 59
def prefixEnd_911617 : Nat := 4983230072969 + 3 ^ 40 * 911617 * 2
def baseEnd_911617 : Nat := 34673903245175187258893

theorem tailTrace_911617 : CollatzResearch.WordTrace tailWord_911617 prefixEnd_911617 34673903245175187258893 := by
  unfold tailWord_911617
  simp only [CollatzResearch.WordTrace]
  refine ⟨33249403538374775633453105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22166269025583183755635403 33249403538374775633453105)
  ·
    refine ⟨24937052653781081725089829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33249403538374775633453105 24937052653781081725089829)
    ·
      refine ⟨4675697372583952823454343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24937052653781081725089829 4675697372583952823454343)
      ·
        refine ⟨7013546058875929235181515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4675697372583952823454343 7013546058875929235181515)
        ·
          refine ⟨10520319088313893852772273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7013546058875929235181515 10520319088313893852772273)
          ·
            refine ⟨7890239316235420389579205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10520319088313893852772273 7890239316235420389579205)
            ·
              refine ⟨1479419871794141323046101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7890239316235420389579205 1479419871794141323046101)
              ·
                refine ⟨34673903245175187258893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1479419871794141323046101 34673903245175187258893)
                ·
                  rfl

theorem cell22_911617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 7].length) (baseStart_911617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_911617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_911617 prefixEnd_911617 := by exact prefixLift 911617
  have htrace : WordTrace (prefixWord ++ tailWord_911617) baseStart_911617 baseEnd_911617 := by
    simpa [prefixWord, tailWord_911617, baseEnd_911617] using wordTrace_append hprefix tailTrace_911617
  have hstable : (prefixWord ++ tailWord_911617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911617).length < 2 ^ (prefixWord ++ tailWord_911617).sum := by decide
  have hdescent : baseEnd_911617 < baseStart_911617 := by decide
  rcases family_descends (prefixWord ++ tailWord_911617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911739 : List Nat := [1, 1, 1, 1, 1, 7, 3, 1, 1, 5]
def baseStart_911739 : Nat := 118140960795 + 911739 * 2 ^ 59
def prefixEnd_911739 : Nat := 4983230072969 + 3 ^ 40 * 911739 * 2
def baseEnd_911739 : Nat := 312106892299809033779663

theorem tailTrace_911739 : CollatzResearch.WordTrace tailWord_911739 prefixEnd_911739 312106892299809033779663 := by
  unfold tailWord_911739
  simp only [CollatzResearch.WordTrace]
  refine ⟨33253853243932790469394271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22169235495955193646262847 33253853243932790469394271)
  ·
    refine ⟨49880779865899185704091407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33253853243932790469394271 49880779865899185704091407)
    ·
      refine ⟨74821169798848778556137111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49880779865899185704091407 74821169798848778556137111)
      ·
        refine ⟨112231754698273167834205667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74821169798848778556137111 112231754698273167834205667)
        ·
          refine ⟨168347632047409751751308501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112231754698273167834205667 168347632047409751751308501)
          ·
            refine ⟨3945647626111166056671293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 168347632047409751751308501 3945647626111166056671293)
            ·
              refine ⟨1479617859791687271251735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3945647626111166056671293 1479617859791687271251735)
              ·
                refine ⟨2219426789687530906877603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1479617859791687271251735 2219426789687530906877603)
                ·
                  refine ⟨3329140184531296360316405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2219426789687530906877603 3329140184531296360316405)
                  ·
                    refine ⟨312106892299809033779663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3329140184531296360316405 312106892299809033779663)
                    ·
                      rfl

theorem cell22_911739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 1, 1, 5].length) (baseStart_911739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_911739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_911739 prefixEnd_911739 := by exact prefixLift 911739
  have htrace : WordTrace (prefixWord ++ tailWord_911739) baseStart_911739 baseEnd_911739 := by
    simpa [prefixWord, tailWord_911739, baseEnd_911739] using wordTrace_append hprefix tailTrace_911739
  have hstable : (prefixWord ++ tailWord_911739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911739).length < 2 ^ (prefixWord ++ tailWord_911739).sum := by decide
  have hdescent : baseEnd_911739 < baseStart_911739 := by decide
  rcases family_descends (prefixWord ++ tailWord_911739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911758 : List Nat := [4, 1, 1, 4, 1, 1, 3, 3, 4]
def baseStart_911758 : Nat := 118140960795 + 911758 * 2 ^ 59
def prefixEnd_911758 : Nat := 4983230072969 + 3 ^ 40 * 911758 * 2
def baseEnd_911758 : Nat := 104037798796033105851535

theorem tailTrace_911758 : CollatzResearch.WordTrace tailWord_911758 prefixEnd_911758 104037798796033105851535 := by
  unfold tailWord_911758
  simp only [CollatzResearch.WordTrace]
  refine ⟨4156818278857994589291991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22169697487242637809557285 4156818278857994589291991)
  ·
    refine ⟨6235227418286991883937987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4156818278857994589291991 6235227418286991883937987)
    ·
      refine ⟨9352841127430487825906981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6235227418286991883937987 9352841127430487825906981)
      ·
        refine ⟨1753657711393216467357559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9352841127430487825906981 1753657711393216467357559)
        ·
          refine ⟨2630486567089824701036339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1753657711393216467357559 2630486567089824701036339)
          ·
            refine ⟨3945729850634737051554509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2630486567089824701036339 3945729850634737051554509)
            ·
              refine ⟨1479648693988026394332941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3945729850634737051554509 1479648693988026394332941)
              ·
                refine ⟨554868260245509897874853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1479648693988026394332941 554868260245509897874853)
                ·
                  refine ⟨104037798796033105851535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 554868260245509897874853 104037798796033105851535)
                  ·
                    rfl

theorem cell22_911758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 3, 4].length) (baseStart_911758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_911758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_911758 prefixEnd_911758 := by exact prefixLift 911758
  have htrace : WordTrace (prefixWord ++ tailWord_911758) baseStart_911758 baseEnd_911758 := by
    simpa [prefixWord, tailWord_911758, baseEnd_911758] using wordTrace_append hprefix tailTrace_911758
  have hstable : (prefixWord ++ tailWord_911758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911758).length < 2 ^ (prefixWord ++ tailWord_911758).sum := by decide
  have hdescent : baseEnd_911758 < baseStart_911758 := by decide
  rcases family_descends (prefixWord ++ tailWord_911758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911818 : List Nat := [3, 1, 2, 1, 2, 2, 2, 5, 1, 3]
def baseStart_911818 : Nat := 118140960795 + 911818 * 2 ^ 59
def prefixEnd_911818 : Nat := 4983230072969 + 3 ^ 40 * 911818 * 2
def baseEnd_911818 : Nat := 312133935614279161054421

theorem tailTrace_911818 : CollatzResearch.WordTrace tailWord_911818 prefixEnd_911818 312133935614279161054421 := by
  unfold tailWord_911818
  simp only [CollatzResearch.WordTrace]
  refine ⟨8314183652661646740380027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22171156407097724641013405 8314183652661646740380027)
  ·
    refine ⟨12471275478992470110570041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8314183652661646740380027 12471275478992470110570041)
    ·
      refine ⟨9353456609244352582927531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12471275478992470110570041 9353456609244352582927531)
      ·
        refine ⟨14030184913866528874391297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9353456609244352582927531 14030184913866528874391297)
        ·
          refine ⟨10522638685399896655793473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14030184913866528874391297 10522638685399896655793473)
          ·
            refine ⟨7891979014049922491845105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10522638685399896655793473 7891979014049922491845105)
            ·
              refine ⟨5918984260537441868883829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7891979014049922491845105 5918984260537441868883829)
              ·
                refine ⟨554904774425385175207859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5918984260537441868883829 554904774425385175207859)
                ·
                  refine ⟨832357161638077762811789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 554904774425385175207859 832357161638077762811789)
                  ·
                    refine ⟨312133935614279161054421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 832357161638077762811789 312133935614279161054421)
                    ·
                      rfl

theorem cell22_911818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 5, 1, 3].length) (baseStart_911818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_911818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_911818 prefixEnd_911818 := by exact prefixLift 911818
  have htrace : WordTrace (prefixWord ++ tailWord_911818) baseStart_911818 baseEnd_911818 := by
    simpa [prefixWord, tailWord_911818, baseEnd_911818] using wordTrace_append hprefix tailTrace_911818
  have hstable : (prefixWord ++ tailWord_911818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911818).length < 2 ^ (prefixWord ++ tailWord_911818).sum := by decide
  have hdescent : baseEnd_911818 < baseStart_911818 := by decide
  rcases family_descends (prefixWord ++ tailWord_911818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911859 : List Nat := [1, 1, 1, 2, 2, 2, 5, 2, 6]
def baseStart_911859 : Nat := 118140960795 + 911859 * 2 ^ 59
def prefixEnd_911859 : Nat := 4983230072969 + 3 ^ 40 * 911859 * 2
def baseEnd_911859 : Nat := 104049323584056240259765

theorem tailTrace_911859 : CollatzResearch.WordTrace tailWord_911859 prefixEnd_911859 104049323584056240259765 := by
  unfold tailWord_911859
  simp only [CollatzResearch.WordTrace]
  refine ⟨33258230003498050963762631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22172153335665367309175087 33258230003498050963762631)
  ·
    refine ⟨49887345005247076445643947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33258230003498050963762631 49887345005247076445643947)
    ·
      refine ⟨74831017507870614668465921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49887345005247076445643947 74831017507870614668465921)
      ·
        refine ⟨56123263130902961001349441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74831017507870614668465921 56123263130902961001349441)
        ·
          refine ⟨42092447348177220751012081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56123263130902961001349441 42092447348177220751012081)
          ·
            refine ⟨31569335511132915563259061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42092447348177220751012081 31569335511132915563259061)
            ·
              refine ⟨2959625204168710834055537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31569335511132915563259061 2959625204168710834055537)
              ·
                refine ⟨2219718903126533125541653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2959625204168710834055537 2219718903126533125541653)
                ·
                  refine ⟨104049323584056240259765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2219718903126533125541653 104049323584056240259765)
                  ·
                    rfl

theorem cell22_911859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2, 6].length) (baseStart_911859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_911859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_911859 prefixEnd_911859 := by exact prefixLift 911859
  have htrace : WordTrace (prefixWord ++ tailWord_911859) baseStart_911859 baseEnd_911859 := by
    simpa [prefixWord, tailWord_911859, baseEnd_911859] using wordTrace_append hprefix tailTrace_911859
  have hstable : (prefixWord ++ tailWord_911859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911859).length < 2 ^ (prefixWord ++ tailWord_911859).sum := by decide
  have hdescent : baseEnd_911859 < baseStart_911859 := by decide
  rcases family_descends (prefixWord ++ tailWord_911859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911891 : List Nat := [1, 1, 1, 2, 1, 5, 3, 1, 4, 3]
def baseStart_911891 : Nat := 118140960795 + 911891 * 2 ^ 59
def prefixEnd_911891 : Nat := 4983230072969 + 3 ^ 40 * 911891 * 2
def baseEnd_911891 : Nat := 312158925006131303979197

theorem tailTrace_911891 : CollatzResearch.WordTrace tailWord_911891 prefixEnd_911891 312158925006131303979197 := by
  unfold tailWord_911891
  simp only [CollatzResearch.WordTrace]
  refine ⟨33259397139382120428927527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22172931426254746952618351 33259397139382120428927527)
  ·
    refine ⟨49889095709073180643391291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33259397139382120428927527 49889095709073180643391291)
    ·
      refine ⟨74833643563609770965086937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49889095709073180643391291 74833643563609770965086937)
      ·
        refine ⟨56125232672707328223815203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74833643563609770965086937 56125232672707328223815203)
        ·
          refine ⟨84187849009060992335722805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56125232672707328223815203 84187849009060992335722805)
          ·
            refine ⟨7892610844599468031474013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84187849009060992335722805 7892610844599468031474013)
            ·
              refine ⟨2959729066724800511802755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7892610844599468031474013 2959729066724800511802755)
              ·
                refine ⟨4439593600087200767704133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2959729066724800511802755 4439593600087200767704133)
                ·
                  refine ⟨832423800016350143944525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4439593600087200767704133 832423800016350143944525)
                  ·
                    refine ⟨312158925006131303979197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 832423800016350143944525 312158925006131303979197)
                    ·
                      rfl

theorem cell22_911891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 4, 3].length) (baseStart_911891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_911891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_911891 prefixEnd_911891 := by exact prefixLift 911891
  have htrace : WordTrace (prefixWord ++ tailWord_911891) baseStart_911891 baseEnd_911891 := by
    simpa [prefixWord, tailWord_911891, baseEnd_911891] using wordTrace_append hprefix tailTrace_911891
  have hstable : (prefixWord ++ tailWord_911891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911891).length < 2 ^ (prefixWord ++ tailWord_911891).sum := by decide
  have hdescent : baseEnd_911891 < baseStart_911891 := by decide
  rcases family_descends (prefixWord ++ tailWord_911891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911921 : List Nat := [1, 2, 2, 3, 1, 1, 6, 6]
def baseStart_911921 : Nat := 118140960795 + 911921 * 2 ^ 59
def prefixEnd_911921 : Nat := 4983230072969 + 3 ^ 40 * 911921 * 2
def baseEnd_911921 : Nat := 34685466068802358414345

theorem tailTrace_911921 : CollatzResearch.WordTrace tailWord_911921 prefixEnd_911921 34685466068802358414345 := by
  unfold tailWord_911921
  simp only [CollatzResearch.WordTrace]
  refine ⟨33260491329273435552519617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22173660886182290368346411 33260491329273435552519617)
  ·
    refine ⟨24945368496955076664389713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33260491329273435552519617 24945368496955076664389713)
    ·
      refine ⟨18709026372716307498292285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24945368496955076664389713 18709026372716307498292285)
      ·
        refine ⟨7015884889768615311859607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18709026372716307498292285 7015884889768615311859607)
        ·
          refine ⟨10523827334652922967789411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7015884889768615311859607 10523827334652922967789411)
          ·
            refine ⟨15785741001979384451684117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10523827334652922967789411 15785741001979384451684117)
            ·
              refine ⟨739956609467783646172693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15785741001979384451684117 739956609467783646172693)
              ·
                refine ⟨34685466068802358414345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 739956609467783646172693 34685466068802358414345)
                ·
                  rfl

theorem cell22_911921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 6].length) (baseStart_911921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_911921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_911921 prefixEnd_911921 := by exact prefixLift 911921
  have htrace : WordTrace (prefixWord ++ tailWord_911921) baseStart_911921 baseEnd_911921 := by
    simpa [prefixWord, tailWord_911921, baseEnd_911921] using wordTrace_append hprefix tailTrace_911921
  have hstable : (prefixWord ++ tailWord_911921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911921).length < 2 ^ (prefixWord ++ tailWord_911921).sum := by decide
  have hdescent : baseEnd_911921 < baseStart_911921 := by decide
  rcases family_descends (prefixWord ++ tailWord_911921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911936 : List Nat := [2, 1, 1, 2, 2, 2, 2, 2, 5, 3]
def baseStart_911936 : Nat := 118140960795 + 911936 * 2 ^ 59
def prefixEnd_911936 : Nat := 4983230072969 + 3 ^ 40 * 911936 * 2
def baseEnd_911936 : Nat := 312174329425766186604059

theorem tailTrace_911936 : CollatzResearch.WordTrace tailWord_911936 prefixEnd_911936 312174329425766186604059 := by
  unfold tailWord_911936
  simp only [CollatzResearch.WordTrace]
  refine ⟨16630519212109546557157831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22174025616146062076210441 16630519212109546557157831)
  ·
    refine ⟨24945778818164319835736747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16630519212109546557157831 24945778818164319835736747)
    ·
      refine ⟨37418668227246479753605121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24945778818164319835736747 37418668227246479753605121)
      ·
        refine ⟨28064001170434859815203841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37418668227246479753605121 28064001170434859815203841)
        ·
          refine ⟨21048000877826144861402881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28064001170434859815203841 21048000877826144861402881)
          ·
            refine ⟨15786000658369608646052161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21048000877826144861402881 15786000658369608646052161)
            ·
              refine ⟨11839500493777206484539121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15786000658369608646052161 11839500493777206484539121)
              ·
                refine ⟨8879625370332904863404341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11839500493777206484539121 8879625370332904863404341)
                ·
                  refine ⟨832464878468709830944157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8879625370332904863404341 832464878468709830944157)
                  ·
                    refine ⟨312174329425766186604059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 832464878468709830944157 312174329425766186604059)
                    ·
                      rfl

theorem cell22_911936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 5, 3].length) (baseStart_911936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_911936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_911936 prefixEnd_911936 := by exact prefixLift 911936
  have htrace : WordTrace (prefixWord ++ tailWord_911936) baseStart_911936 baseEnd_911936 := by
    simpa [prefixWord, tailWord_911936, baseEnd_911936] using wordTrace_append hprefix tailTrace_911936
  have hstable : (prefixWord ++ tailWord_911936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911936).length < 2 ^ (prefixWord ++ tailWord_911936).sum := by decide
  have hdescent : baseEnd_911936 < baseStart_911936 := by decide
  rcases family_descends (prefixWord ++ tailWord_911936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911953 : List Nat := [1, 2, 2, 1, 3, 3, 3, 1, 3, 3]
def baseStart_911953 : Nat := 118140960795 + 911953 * 2 ^ 59
def prefixEnd_911953 : Nat := 4983230072969 + 3 ^ 40 * 911953 * 2
def baseEnd_911953 : Nat := 312180148873183808929007

theorem tailTrace_911953 : CollatzResearch.WordTrace tailWord_911953 prefixEnd_911953 312180148873183808929007 := by
  unfold tailWord_911953
  simp only [CollatzResearch.WordTrace]
  refine ⟨33261658465157505017684513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22174438976771670011789675 33261658465157505017684513)
  ·
    refine ⟨24946243848868128763263385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33261658465157505017684513 24946243848868128763263385)
    ·
      refine ⟨18709682886651096572447539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24946243848868128763263385 18709682886651096572447539)
      ·
        refine ⟨28064524329976644858671309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18709682886651096572447539 28064524329976644858671309)
        ·
          refine ⟨10524196623741241822001741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28064524329976644858671309 10524196623741241822001741)
          ·
            refine ⟨3946573733902965683250653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10524196623741241822001741 3946573733902965683250653)
            ·
              refine ⟨1479965150213612131218995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3946573733902965683250653 1479965150213612131218995)
              ·
                refine ⟨2219947725320418196828493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1479965150213612131218995 2219947725320418196828493)
                ·
                  refine ⟨832480396995156823810685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2219947725320418196828493 832480396995156823810685)
                  ·
                    refine ⟨312180148873183808929007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 832480396995156823810685 312180148873183808929007)
                    ·
                      rfl

theorem cell22_911953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 1, 3, 3].length) (baseStart_911953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_911953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_911953 prefixEnd_911953 := by exact prefixLift 911953
  have htrace : WordTrace (prefixWord ++ tailWord_911953) baseStart_911953 baseEnd_911953 := by
    simpa [prefixWord, tailWord_911953, baseEnd_911953] using wordTrace_append hprefix tailTrace_911953
  have hstable : (prefixWord ++ tailWord_911953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911953).length < 2 ^ (prefixWord ++ tailWord_911953).sum := by decide
  have hdescent : baseEnd_911953 < baseStart_911953 := by decide
  rcases family_descends (prefixWord ++ tailWord_911953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912004 : List Nat := [2, 3, 2, 1, 3, 3, 2, 2, 1, 3]
def baseStart_912004 : Nat := 118140960795 + 912004 * 2 ^ 59
def prefixEnd_912004 : Nat := 4983230072969 + 3 ^ 40 * 912004 * 2
def baseEnd_912004 : Nat := 312197607215436675903851

theorem tailTrace_912004 : CollatzResearch.WordTrace tailWord_912004 prefixEnd_912004 312197607215436675903851 := by
  unfold tailWord_912004
  simp only [CollatzResearch.WordTrace]
  refine ⟨16631759293986370363895533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22175679058648493818527377 16631759293986370363895533)
  ·
    refine ⟨6236909735244888886460825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16631759293986370363895533 6236909735244888886460825)
    ·
      refine ⟨4677682301433666664845619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6236909735244888886460825 4677682301433666664845619)
      ·
        refine ⟨7016523452150499997268429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4677682301433666664845619 7016523452150499997268429)
        ·
          refine ⟨2631196294556437498975661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7016523452150499997268429 2631196294556437498975661)
          ·
            refine ⟨986698610458664062115873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2631196294556437498975661 986698610458664062115873)
            ·
              refine ⟨740023957843998046586905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 986698610458664062115873 740023957843998046586905)
              ·
                refine ⟨555017968382998534940179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 740023957843998046586905 555017968382998534940179)
                ·
                  refine ⟨832526952574497802410269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 555017968382998534940179 832526952574497802410269)
                  ·
                    refine ⟨312197607215436675903851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 832526952574497802410269 312197607215436675903851)
                    ·
                      rfl

theorem cell22_912004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 2, 1, 3].length) (baseStart_912004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_912004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_912004 prefixEnd_912004 := by exact prefixLift 912004
  have htrace : WordTrace (prefixWord ++ tailWord_912004) baseStart_912004 baseEnd_912004 := by
    simpa [prefixWord, tailWord_912004, baseEnd_912004] using wordTrace_append hprefix tailTrace_912004
  have hstable : (prefixWord ++ tailWord_912004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912004).length < 2 ^ (prefixWord ++ tailWord_912004).sum := by decide
  have hdescent : baseEnd_912004 < baseStart_912004 := by decide
  rcases family_descends (prefixWord ++ tailWord_912004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912028 : List Nat := [2, 2, 3, 2, 2, 2, 1, 2, 6]
def baseStart_912028 : Nat := 118140960795 + 912028 * 2 ^ 59
def prefixEnd_912028 : Nat := 4983230072969 + 3 ^ 40 * 912028 * 2
def baseEnd_912028 : Nat := 104068607635302871101259

theorem tailTrace_912028 : CollatzResearch.WordTrace tailWord_912028 prefixEnd_912028 104068607635302871101259 := by
  unfold tailWord_912028
  simp only [CollatzResearch.WordTrace]
  refine ⟨16632196969942896413332369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22176262626590528551109825 16632196969942896413332369)
  ·
    refine ⟨12474147727457172309999277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16632196969942896413332369 12474147727457172309999277)
    ·
      refine ⟨4677805397796439616249729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12474147727457172309999277 4677805397796439616249729)
      ·
        refine ⟨3508354048347329712187297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4677805397796439616249729 3508354048347329712187297)
        ·
          refine ⟨2631265536260497284140473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3508354048347329712187297 2631265536260497284140473)
          ·
            refine ⟨1973449152195372963105355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2631265536260497284140473 1973449152195372963105355)
            ·
              refine ⟨2960173728293059444658033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1973449152195372963105355 2960173728293059444658033)
              ·
                refine ⟨2220130296219794583493525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2960173728293059444658033 2220130296219794583493525)
                ·
                  refine ⟨104068607635302871101259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2220130296219794583493525 104068607635302871101259)
                  ·
                    rfl

theorem cell22_912028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 2, 6].length) (baseStart_912028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_912028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_912028 prefixEnd_912028 := by exact prefixLift 912028
  have htrace : WordTrace (prefixWord ++ tailWord_912028) baseStart_912028 baseEnd_912028 := by
    simpa [prefixWord, tailWord_912028, baseEnd_912028] using wordTrace_append hprefix tailTrace_912028
  have hstable : (prefixWord ++ tailWord_912028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912028).length < 2 ^ (prefixWord ++ tailWord_912028).sum := by decide
  have hdescent : baseEnd_912028 < baseStart_912028 := by decide
  rcases family_descends (prefixWord ++ tailWord_912028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912030 : List Nat := [4, 3, 1, 1, 1, 1, 2, 4, 1, 4]
def baseStart_912030 : Nat := 118140960795 + 912030 * 2 ^ 59
def prefixEnd_912030 : Nat := 4983230072969 + 3 ^ 40 * 912030 * 2
def baseEnd_912030 : Nat := 312206507546781274753771

theorem tailTrace_912030 : CollatzResearch.WordTrace tailWord_912030 prefixEnd_912030 312206507546781274753771 := by
  unfold tailWord_912030
  simp only [CollatzResearch.WordTrace]
  refine ⟨4158058360734818396029693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22176311257252364778825029 4158058360734818396029693)
  ·
    refine ⟨1559271885275556898511135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4158058360734818396029693 1559271885275556898511135)
    ·
      refine ⟨2338907827913335347766703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1559271885275556898511135 2338907827913335347766703)
      ·
        refine ⟨3508361741870003021650055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2338907827913335347766703 3508361741870003021650055)
        ·
          refine ⟨5262542612805004532475083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3508361741870003021650055 5262542612805004532475083)
          ·
            refine ⟨7893813919207506798712625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5262542612805004532475083 7893813919207506798712625)
            ·
              refine ⟨5920360439405630099034469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7893813919207506798712625 5920360439405630099034469)
              ·
                refine ⟨1110067582388555643568963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5920360439405630099034469 1110067582388555643568963)
                ·
                  refine ⟨1665101373582833465353445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1110067582388555643568963 1665101373582833465353445)
                  ·
                    refine ⟨312206507546781274753771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1665101373582833465353445 312206507546781274753771)
                    ·
                      rfl

theorem cell22_912030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_912030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_912030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_912030 prefixEnd_912030 := by exact prefixLift 912030
  have htrace : WordTrace (prefixWord ++ tailWord_912030) baseStart_912030 baseEnd_912030 := by
    simpa [prefixWord, tailWord_912030, baseEnd_912030] using wordTrace_append hprefix tailTrace_912030
  have hstable : (prefixWord ++ tailWord_912030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912030).length < 2 ^ (prefixWord ++ tailWord_912030).sum := by decide
  have hdescent : baseEnd_912030 < baseStart_912030 := by decide
  rcases family_descends (prefixWord ++ tailWord_912030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912045 : List Nat := [1, 5, 2, 1, 1, 2, 1, 5, 4]
def baseStart_912045 : Nat := 118140960795 + 912045 * 2 ^ 59
def prefixEnd_912045 : Nat := 4983230072969 + 3 ^ 40 * 912045 * 2
def baseEnd_912045 : Nat := 104070547451108745209575

theorem tailTrace_912045 : CollatzResearch.WordTrace tailWord_912045 prefixEnd_912045 104070547451108745209575 := by
  unfold tailWord_912045
  simp only [CollatzResearch.WordTrace]
  refine ⟨33265013980824204730033589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22176675987216136486689059 33265013980824204730033589)
  ·
    refine ⟨3118595060702269193440649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33265013980824204730033589 3118595060702269193440649)
    ·
      refine ⟨2338946295526701895080487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3118595060702269193440649 2338946295526701895080487)
      ·
        refine ⟨3508419443290052842620731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2338946295526701895080487 3508419443290052842620731)
        ·
          refine ⟨5262629164935079263931097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3508419443290052842620731 5262629164935079263931097)
          ·
            refine ⟨3946971873701309447948323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5262629164935079263931097 3946971873701309447948323)
            ·
              refine ⟨5920457810551964171922485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3946971873701309447948323 5920457810551964171922485)
              ·
                refine ⟨555042919739246641117733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5920457810551964171922485 555042919739246641117733)
                ·
                  refine ⟨104070547451108745209575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 555042919739246641117733 104070547451108745209575)
                  ·
                    rfl

theorem cell22_912045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_912045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_912045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_912045 prefixEnd_912045 := by exact prefixLift 912045
  have htrace : WordTrace (prefixWord ++ tailWord_912045) baseStart_912045 baseEnd_912045 := by
    simpa [prefixWord, tailWord_912045, baseEnd_912045] using wordTrace_append hprefix tailTrace_912045
  have hstable : (prefixWord ++ tailWord_912045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912045).length < 2 ^ (prefixWord ++ tailWord_912045).sum := by decide
  have hdescent : baseEnd_912045 < baseStart_912045 := by decide
  rcases family_descends (prefixWord ++ tailWord_912045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912118 : List Nat := [5, 1, 1, 1, 1, 2, 1, 3, 7]
def baseStart_912118 : Nat := 118140960795 + 912118 * 2 ^ 59
def prefixEnd_912118 : Nat := 4983230072969 + 3 ^ 40 * 912118 * 2
def baseEnd_912118 : Nat := 104078877248392792851167

theorem tailTrace_912118 : CollatzResearch.WordTrace tailWord_912118 prefixEnd_912118 104078877248392792851167 := by
  unfold tailWord_912118
  simp only [CollatzResearch.WordTrace]
  refine ⟨2079229781847483637340063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22178451006373158798294005 2079229781847483637340063)
  ·
    refine ⟨3118844672771225456010095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2079229781847483637340063 3118844672771225456010095)
    ·
      refine ⟨4678267009156838184015143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3118844672771225456010095 4678267009156838184015143)
      ·
        refine ⟨7017400513735257276022715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4678267009156838184015143 7017400513735257276022715)
        ·
          refine ⟨10526100770602885914034073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7017400513735257276022715 10526100770602885914034073)
          ·
            refine ⟨7894575577952164435525555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10526100770602885914034073 7894575577952164435525555)
            ·
              refine ⟨11841863366928246653288333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7894575577952164435525555 11841863366928246653288333)
              ·
                refine ⟨4440698762598092494983125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11841863366928246653288333 4440698762598092494983125)
                ·
                  refine ⟨104078877248392792851167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4440698762598092494983125 104078877248392792851167)
                  ·
                    rfl

theorem cell22_912118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_912118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_912118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_912118 prefixEnd_912118 := by exact prefixLift 912118
  have htrace : WordTrace (prefixWord ++ tailWord_912118) baseStart_912118 baseEnd_912118 := by
    simpa [prefixWord, tailWord_912118, baseEnd_912118] using wordTrace_append hprefix tailTrace_912118
  have hstable : (prefixWord ++ tailWord_912118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912118).length < 2 ^ (prefixWord ++ tailWord_912118).sum := by decide
  have hdescent : baseEnd_912118 < baseStart_912118 := by decide
  rcases family_descends (prefixWord ++ tailWord_912118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912131 : List Nat := [1, 1, 1, 3, 2, 2, 1, 1, 2, 8]
def baseStart_912131 : Nat := 118140960795 + 912131 * 2 ^ 59
def prefixEnd_912131 : Nat := 4983230072969 + 3 ^ 40 * 912131 * 2
def baseEnd_912131 : Nat := 312241081910850677978461

theorem tailTrace_912131 : CollatzResearch.WordTrace tailWord_912131 prefixEnd_912131 312241081910850677978461 := by
  unfold tailWord_912131
  simp only [CollatzResearch.WordTrace]
  refine ⟨33268150658512641417664247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22178767105675094278442831 33268150658512641417664247)
  ·
    refine ⟨49902225987768962126496371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33268150658512641417664247 49902225987768962126496371)
    ·
      refine ⟨74853338981653443189744557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49902225987768962126496371 74853338981653443189744557)
      ·
        refine ⟨28070002118120041196154209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74853338981653443189744557 28070002118120041196154209)
        ·
          refine ⟨21052501588590030897115657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28070002118120041196154209 21052501588590030897115657)
          ·
            refine ⟨15789376191442523172836743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21052501588590030897115657 15789376191442523172836743)
            ·
              refine ⟨23684064287163784759255115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15789376191442523172836743 23684064287163784759255115)
              ·
                refine ⟨35526096430745677138882673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23684064287163784759255115 35526096430745677138882673)
                ·
                  refine ⟨26644572323059257854162005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35526096430745677138882673 26644572323059257854162005)
                  ·
                    refine ⟨312241081910850677978461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 26644572323059257854162005 312241081910850677978461)
                    ·
                      rfl

theorem cell22_912131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 8].length) (baseStart_912131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_912131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_912131 prefixEnd_912131 := by exact prefixLift 912131
  have htrace : WordTrace (prefixWord ++ tailWord_912131) baseStart_912131 baseEnd_912131 := by
    simpa [prefixWord, tailWord_912131, baseEnd_912131] using wordTrace_append hprefix tailTrace_912131
  have hstable : (prefixWord ++ tailWord_912131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912131).length < 2 ^ (prefixWord ++ tailWord_912131).sum := by decide
  have hdescent : baseEnd_912131 < baseStart_912131 := by decide
  rcases family_descends (prefixWord ++ tailWord_912131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912135 : List Nat := [1, 1, 4, 4, 1, 2, 1, 3, 5]
def baseStart_912135 : Nat := 118140960795 + 912135 * 2 ^ 59
def prefixEnd_912135 : Nat := 4983230072969 + 3 ^ 40 * 912135 * 2
def baseEnd_912135 : Nat := 104080817064198666959483

theorem tailTrace_912135 : CollatzResearch.WordTrace tailWord_912135 prefixEnd_912135 104080817064198666959483 := by
  unfold tailWord_912135
  simp only [CollatzResearch.WordTrace]
  refine ⟨33268296550498150100809859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22178864366998766733873239 33268296550498150100809859)
  ·
    refine ⟨49902444825747225151214789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33268296550498150100809859 49902444825747225151214789)
    ·
      refine ⟨9356708404827604715852773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49902444825747225151214789 9356708404827604715852773)
      ·
        refine ⟨1754382825905175884222395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9356708404827604715852773 1754382825905175884222395)
        ·
          refine ⟨2631574238857763826333593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1754382825905175884222395 2631574238857763826333593)
          ·
            refine ⟨1973680679143322869750195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2631574238857763826333593 1973680679143322869750195)
            ·
              refine ⟨2960521018714984304625293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1973680679143322869750195 2960521018714984304625293)
              ·
                refine ⟨1110195382018119114234485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2960521018714984304625293 1110195382018119114234485)
                ·
                  refine ⟨104080817064198666959483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1110195382018119114234485 104080817064198666959483)
                  ·
                    rfl

theorem cell22_912135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 3, 5].length) (baseStart_912135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_912135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_912135 prefixEnd_912135 := by exact prefixLift 912135
  have htrace : WordTrace (prefixWord ++ tailWord_912135) baseStart_912135 baseEnd_912135 := by
    simpa [prefixWord, tailWord_912135, baseEnd_912135] using wordTrace_append hprefix tailTrace_912135
  have hstable : (prefixWord ++ tailWord_912135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912135).length < 2 ^ (prefixWord ++ tailWord_912135).sum := by decide
  have hdescent : baseEnd_912135 < baseStart_912135 := by decide
  rcases family_descends (prefixWord ++ tailWord_912135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912178 : List Nat := [3, 2, 1, 1, 3, 1, 1, 2, 3, 5]
def baseStart_912178 : Nat := 118140960795 + 912178 * 2 ^ 59
def prefixEnd_912178 : Nat := 4983230072969 + 3 ^ 40 * 912178 * 2
def baseEnd_912178 : Nat := 312257170971358222053317

theorem tailTrace_912178 : CollatzResearch.WordTrace tailWord_912178 prefixEnd_912178 312257170971358222053317 := by
  unfold tailWord_912178
  simp only [CollatzResearch.WordTrace]
  refine ⟨8317466222335592111156297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22179909926228245629750125 8317466222335592111156297)
  ·
    refine ⟨6238099666751694083367223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8317466222335592111156297 6238099666751694083367223)
    ·
      refine ⟨9357149500127541125050835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6238099666751694083367223 9357149500127541125050835)
      ·
        refine ⟨14035724250191311687576253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9357149500127541125050835 14035724250191311687576253)
        ·
          refine ⟨5263396593821741882841095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14035724250191311687576253 5263396593821741882841095)
          ·
            refine ⟨7895094890732612824261643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5263396593821741882841095 7895094890732612824261643)
            ·
              refine ⟨11842642336098919236392465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7895094890732612824261643 11842642336098919236392465)
              ·
                refine ⟨8881981752074189427294349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11842642336098919236392465 8881981752074189427294349)
                ·
                  refine ⟨3330743157027821035235381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8881981752074189427294349 3330743157027821035235381)
                  ·
                    refine ⟨312257170971358222053317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3330743157027821035235381 312257170971358222053317)
                    ·
                      rfl

theorem cell22_912178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_912178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_912178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_912178 prefixEnd_912178 := by exact prefixLift 912178
  have htrace : WordTrace (prefixWord ++ tailWord_912178) baseStart_912178 baseEnd_912178 := by
    simpa [prefixWord, tailWord_912178, baseEnd_912178] using wordTrace_append hprefix tailTrace_912178
  have hstable : (prefixWord ++ tailWord_912178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912178).length < 2 ^ (prefixWord ++ tailWord_912178).sum := by decide
  have hdescent : baseEnd_912178 < baseStart_912178 := by decide
  rcases family_descends (prefixWord ++ tailWord_912178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912195 : List Nat := [1, 1, 1, 3, 1, 4, 1, 5, 2, 3]
def baseStart_912195 : Nat := 118140960795 + 912195 * 2 ^ 59
def prefixEnd_912195 : Nat := 4983230072969 + 3 ^ 40 * 912195 * 2
def baseEnd_912195 : Nat := 312262990418775844378265

theorem tailTrace_912195 : CollatzResearch.WordTrace tailWord_912195 prefixEnd_912195 312262990418775844378265 := by
  unfold tailWord_912195
  simp only [CollatzResearch.WordTrace]
  refine ⟨33270484930280780347994039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22180323286853853565329359 33270484930280780347994039)
  ·
    refine ⟨49905727395421170521991059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33270484930280780347994039 49905727395421170521991059)
    ·
      refine ⟨74858591093131755782986589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49905727395421170521991059 74858591093131755782986589)
      ·
        refine ⟨28071971659924408418619971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74858591093131755782986589 28071971659924408418619971)
        ·
          refine ⟨42107957489886612627929957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28071971659924408418619971 42107957489886612627929957)
          ·
            refine ⟨7895242029353739867736867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42107957489886612627929957 7895242029353739867736867)
            ·
              refine ⟨11842863044030609801605301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7895242029353739867736867 11842863044030609801605301)
              ·
                refine ⟨1110268410377869668900497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11842863044030609801605301 1110268410377869668900497)
                ·
                  refine ⟨832701307783402251675373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1110268410377869668900497 832701307783402251675373)
                  ·
                    refine ⟨312262990418775844378265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 832701307783402251675373 312262990418775844378265)
                    ·
                      rfl

theorem cell22_912195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 5, 2, 3].length) (baseStart_912195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_912195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_912195 prefixEnd_912195 := by exact prefixLift 912195
  have htrace : WordTrace (prefixWord ++ tailWord_912195) baseStart_912195 baseEnd_912195 := by
    simpa [prefixWord, tailWord_912195, baseEnd_912195] using wordTrace_append hprefix tailTrace_912195
  have hstable : (prefixWord ++ tailWord_912195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912195).length < 2 ^ (prefixWord ++ tailWord_912195).sum := by decide
  have hdescent : baseEnd_912195 < baseStart_912195 := by decide
  rcases family_descends (prefixWord ++ tailWord_912195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912240 : List Nat := [2, 1, 1, 1, 4, 1, 3, 3, 3, 3]
def baseStart_912240 : Nat := 118140960795 + 912240 * 2 ^ 59
def prefixEnd_912240 : Nat := 4983230072969 + 3 ^ 40 * 912240 * 2
def baseEnd_912240 : Nat := 312278394838410727003127

theorem tailTrace_912240 : CollatzResearch.WordTrace tailWord_912240 prefixEnd_912240 312278394838410727003127 := by
  unfold tailWord_912240
  simp only [CollatzResearch.WordTrace]
  refine ⟨16636063107558876516691087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22181417476745168688921449 16636063107558876516691087)
  ·
    refine ⟨24954094661338314775036631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16636063107558876516691087 24954094661338314775036631)
    ·
      refine ⟨37431141992007472162554947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24954094661338314775036631 37431141992007472162554947)
      ·
        refine ⟨56146712988011208243832421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37431141992007472162554947 56146712988011208243832421)
        ·
          refine ⟨10527508685252101545718579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56146712988011208243832421 10527508685252101545718579)
          ·
            refine ⟨15791263027878152318577869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10527508685252101545718579 15791263027878152318577869)
            ·
              refine ⟨5921723635454307119466701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15791263027878152318577869 5921723635454307119466701)
              ·
                refine ⟨2220646363295365169800013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5921723635454307119466701 2220646363295365169800013)
                ·
                  refine ⟨832742386235761938675005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2220646363295365169800013 832742386235761938675005)
                  ·
                    refine ⟨312278394838410727003127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 832742386235761938675005 312278394838410727003127)
                    ·
                      rfl

theorem cell22_912240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3, 3, 3].length) (baseStart_912240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_912240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_912240 prefixEnd_912240 := by exact prefixLift 912240
  have htrace : WordTrace (prefixWord ++ tailWord_912240) baseStart_912240 baseEnd_912240 := by
    simpa [prefixWord, tailWord_912240, baseEnd_912240] using wordTrace_append hprefix tailTrace_912240
  have hstable : (prefixWord ++ tailWord_912240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912240).length < 2 ^ (prefixWord ++ tailWord_912240).sum := by decide
  have hdescent : baseEnd_912240 < baseStart_912240 := by decide
  rcases family_descends (prefixWord ++ tailWord_912240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912246 : List Nat := [5, 1, 1, 3, 1, 2, 3, 1, 2, 3]
def baseStart_912246 : Nat := 118140960795 + 912246 * 2 ^ 59
def prefixEnd_912246 : Nat := 4983230072969 + 3 ^ 40 * 912246 * 2
def baseEnd_912246 : Nat := 312280448761028711353109

theorem tailTrace_912246 : CollatzResearch.WordTrace tailWord_912246 prefixEnd_912246 312280448761028711353109 := by
  unfold tailWord_912246
  simp only [CollatzResearch.WordTrace]
  refine ⟨2079521565818501003631287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22181563368730677372067061 2079521565818501003631287)
  ·
    refine ⟨3119282348727751505446931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2079521565818501003631287 3119282348727751505446931)
    ·
      refine ⟨4678923523091627258170397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3119282348727751505446931 4678923523091627258170397)
      ·
        refine ⟨1754596321159360221813899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4678923523091627258170397 1754596321159360221813899)
        ·
          refine ⟨2631894481739040332720849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1754596321159360221813899 2631894481739040332720849)
          ·
            refine ⟨1973920861304280249540637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2631894481739040332720849 1973920861304280249540637)
            ·
              refine ⟨740220322989105093577739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1973920861304280249540637 740220322989105093577739)
              ·
                refine ⟨1110330484483657640366609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 740220322989105093577739 1110330484483657640366609)
                ·
                  refine ⟨832747863362743230274957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1110330484483657640366609 832747863362743230274957)
                  ·
                    refine ⟨312280448761028711353109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 832747863362743230274957 312280448761028711353109)
                    ·
                      rfl

theorem cell22_912246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_912246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_912246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_912246 prefixEnd_912246 := by exact prefixLift 912246
  have htrace : WordTrace (prefixWord ++ tailWord_912246) baseStart_912246 baseEnd_912246 := by
    simpa [prefixWord, tailWord_912246, baseEnd_912246] using wordTrace_append hprefix tailTrace_912246
  have hstable : (prefixWord ++ tailWord_912246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912246).length < 2 ^ (prefixWord ++ tailWord_912246).sum := by decide
  have hdescent : baseEnd_912246 < baseStart_912246 := by decide
  rcases family_descends (prefixWord ++ tailWord_912246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912268 : List Nat := [2, 2, 1, 2, 1, 2, 2, 2, 1, 7]
def baseStart_912268 : Nat := 118140960795 + 912268 * 2 ^ 59
def prefixEnd_912268 : Nat := 4983230072969 + 3 ^ 40 * 912268 * 2
def baseEnd_912268 : Nat := 312287979810627987303041

theorem tailTrace_912268 : CollatzResearch.WordTrace tailWord_912268 prefixEnd_912268 312287979810627987303041 := by
  unfold tailWord_912268
  simp only [CollatzResearch.WordTrace]
  refine ⟨16636573729508156907700729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22182098306010875876934305 16636573729508156907700729)
  ·
    refine ⟨12477430297131117680775547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16636573729508156907700729 12477430297131117680775547)
    ·
      refine ⟨18716145445696676521163321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12477430297131117680775547 18716145445696676521163321)
      ·
        refine ⟨14037109084272507390872491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18716145445696676521163321 14037109084272507390872491)
        ·
          refine ⟨21055663626408761086308737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14037109084272507390872491 21055663626408761086308737)
          ·
            refine ⟨15791747719806570814731553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21055663626408761086308737 15791747719806570814731553)
            ·
              refine ⟨11843810789854928111048665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15791747719806570814731553 11843810789854928111048665)
              ·
                refine ⟨8882858092391196083286499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11843810789854928111048665 8882858092391196083286499)
                ·
                  refine ⟨13324287138586794124929749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8882858092391196083286499 13324287138586794124929749)
                  ·
                    refine ⟨312287979810627987303041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13324287138586794124929749 312287979810627987303041)
                    ·
                      rfl

theorem cell22_912268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 7].length) (baseStart_912268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_912268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_912268 prefixEnd_912268 := by exact prefixLift 912268
  have htrace : WordTrace (prefixWord ++ tailWord_912268) baseStart_912268 baseEnd_912268 := by
    simpa [prefixWord, tailWord_912268, baseEnd_912268] using wordTrace_append hprefix tailTrace_912268
  have hstable : (prefixWord ++ tailWord_912268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912268).length < 2 ^ (prefixWord ++ tailWord_912268).sum := by decide
  have hdescent : baseEnd_912268 < baseStart_912268 := by decide
  rcases family_descends (prefixWord ++ tailWord_912268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912317 : List Nat := [1, 4, 1, 2, 4, 1, 1, 1, 3, 4]
def baseStart_912317 : Nat := 118140960795 + 912317 * 2 ^ 59
def prefixEnd_912317 : Nat := 4983230072969 + 3 ^ 40 * 912317 * 2
def baseEnd_912317 : Nat := 312304753512008192827891

theorem tailTrace_912317 : CollatzResearch.WordTrace tailWord_912317 prefixEnd_912317 312304753512008192827891 := by
  unfold tailWord_912317
  simp only [CollatzResearch.WordTrace]
  refine ⟨33274934635838795183935205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22183289757225863455956803 33274934635838795183935205)
  ·
    refine ⟨6239050244219774096987851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33274934635838795183935205 6239050244219774096987851)
    ·
      refine ⟨9358575366329661145481777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6239050244219774096987851 9358575366329661145481777)
      ·
        refine ⟨7018931524747245859111333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9358575366329661145481777 7018931524747245859111333)
        ·
          refine ⟨1316049660890108598583375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7018931524747245859111333 1316049660890108598583375)
          ·
            refine ⟨1974074491335162897875063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1316049660890108598583375 1974074491335162897875063)
            ·
              refine ⟨2961111737002744346812595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1974074491335162897875063 2961111737002744346812595)
              ·
                refine ⟨4441667605504116520218893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2961111737002744346812595 4441667605504116520218893)
                ·
                  refine ⟨1665625352064043695082085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4441667605504116520218893 1665625352064043695082085)
                  ·
                    refine ⟨312304753512008192827891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1665625352064043695082085 312304753512008192827891)
                    ·
                      rfl

theorem cell22_912317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 3, 4].length) (baseStart_912317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_912317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_912317 prefixEnd_912317 := by exact prefixLift 912317
  have htrace : WordTrace (prefixWord ++ tailWord_912317) baseStart_912317 baseEnd_912317 := by
    simpa [prefixWord, tailWord_912317, baseEnd_912317] using wordTrace_append hprefix tailTrace_912317
  have hstable : (prefixWord ++ tailWord_912317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912317).length < 2 ^ (prefixWord ++ tailWord_912317).sum := by decide
  have hdescent : baseEnd_912317 < baseStart_912317 := by decide
  rcases family_descends (prefixWord ++ tailWord_912317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912332 : List Nat := [2, 2, 1, 4, 1, 1, 2, 5, 4]
def baseStart_912332 : Nat := 118140960795 + 912332 * 2 ^ 59
def prefixEnd_912332 : Nat := 4983230072969 + 3 ^ 40 * 912332 * 2
def baseEnd_912332 : Nat := 104103296106184384567615

theorem tailTrace_912332 : CollatzResearch.WordTrace tailWord_912332 prefixEnd_912332 104103296106184384567615 := by
  unfold tailWord_912332
  simp only [CollatzResearch.WordTrace]
  refine ⟨16637740865392226372865625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22183654487189635163820833 16637740865392226372865625)
  ·
    refine ⟨12478305649044169779649219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16637740865392226372865625 12478305649044169779649219)
    ·
      refine ⟨18717458473566254669473829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12478305649044169779649219 18717458473566254669473829)
      ·
        refine ⟨3509523463793672750526343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18717458473566254669473829 3509523463793672750526343)
        ·
          refine ⟨5264285195690509125789515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3509523463793672750526343 5264285195690509125789515)
          ·
            refine ⟨7896427793535763688684273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5264285195690509125789515 7896427793535763688684273)
            ·
              refine ⟨5922320845151822766513205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7896427793535763688684273 5922320845151822766513205)
              ·
                refine ⟨555217579232983384360613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5922320845151822766513205 555217579232983384360613)
                ·
                  refine ⟨104103296106184384567615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 555217579232983384360613 104103296106184384567615)
                  ·
                    rfl

theorem cell22_912332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 5, 4].length) (baseStart_912332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_912332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_912332 prefixEnd_912332 := by exact prefixLift 912332
  have htrace : WordTrace (prefixWord ++ tailWord_912332) baseStart_912332 baseEnd_912332 := by
    simpa [prefixWord, tailWord_912332, baseEnd_912332] using wordTrace_append hprefix tailTrace_912332
  have hstable : (prefixWord ++ tailWord_912332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912332).length < 2 ^ (prefixWord ++ tailWord_912332).sum := by decide
  have hdescent : baseEnd_912332 < baseStart_912332 := by decide
  rcases family_descends (prefixWord ++ tailWord_912332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912334 : List Nat := [4, 1, 1, 1, 2, 4, 3, 1, 1, 4]
def baseStart_912334 : Nat := 118140960795 + 912334 * 2 ^ 59
def prefixEnd_912334 : Nat := 4983230072969 + 3 ^ 40 * 912334 * 2
def baseEnd_912334 : Nat := 312310572959425815152839

theorem tailTrace_912334 : CollatzResearch.WordTrace tailWord_912334 prefixEnd_912334 312310572959425815152839 := by
  unfold tailWord_912334
  simp only [CollatzResearch.WordTrace]
  refine ⟨4159444334597150885913007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22183703117851471391536037 4159444334597150885913007)
  ·
    refine ⟨6239166501895726328869511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4159444334597150885913007 6239166501895726328869511)
    ·
      refine ⟨9358749752843589493304267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6239166501895726328869511 9358749752843589493304267)
      ·
        refine ⟨14038124629265384239956401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9358749752843589493304267 14038124629265384239956401)
        ·
          refine ⟨10528593471949038179967301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14038124629265384239956401 10528593471949038179967301)
          ·
            refine ⟨1974111275990444658743869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10528593471949038179967301 1974111275990444658743869)
            ·
              refine ⟨740291728496416747028951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1974111275990444658743869 740291728496416747028951)
              ·
                refine ⟨1110437592744625120543427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 740291728496416747028951 1110437592744625120543427)
                ·
                  refine ⟨1665656389116937680815141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1110437592744625120543427 1665656389116937680815141)
                  ·
                    refine ⟨312310572959425815152839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1665656389116937680815141 312310572959425815152839)
                    ·
                      rfl

theorem cell22_912334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 1, 1, 4].length) (baseStart_912334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_912334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_912334 prefixEnd_912334 := by exact prefixLift 912334
  have htrace : WordTrace (prefixWord ++ tailWord_912334) baseStart_912334 baseEnd_912334 := by
    simpa [prefixWord, tailWord_912334, baseEnd_912334] using wordTrace_append hprefix tailTrace_912334
  have hstable : (prefixWord ++ tailWord_912334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912334).length < 2 ^ (prefixWord ++ tailWord_912334).sum := by decide
  have hdescent : baseEnd_912334 < baseStart_912334 := by decide
  rcases family_descends (prefixWord ++ tailWord_912334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912349 : List Nat := [1, 4, 3, 1, 2, 2, 1, 4, 4]
def baseStart_912349 : Nat := 118140960795 + 912349 * 2 ^ 59
def prefixEnd_912349 : Nat := 4983230072969 + 3 ^ 40 * 912349 * 2
def baseEnd_912349 : Nat := 104105235921990258675931

theorem tailTrace_912349 : CollatzResearch.WordTrace tailWord_912349 prefixEnd_912349 104105235921990258675931 := by
  unfold tailWord_912349
  simp only [CollatzResearch.WordTrace]
  refine ⟨33276101771722864649100101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22184067847815243099400067 33276101771722864649100101)
  ·
    refine ⟨6239269082198037121706269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33276101771722864649100101 6239269082198037121706269)
    ·
      refine ⟨2339725905824263920639851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6239269082198037121706269 2339725905824263920639851)
      ·
        refine ⟨3509588858736395880959777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2339725905824263920639851 3509588858736395880959777)
        ·
          refine ⟨2632191644052296910719833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3509588858736395880959777 2632191644052296910719833)
          ·
            refine ⟨1974143733039222683039875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2632191644052296910719833 1974143733039222683039875)
            ·
              refine ⟨2961215599558834024559813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1974143733039222683039875 2961215599558834024559813)
              ·
                refine ⟨555227924917281379604965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2961215599558834024559813 555227924917281379604965)
                ·
                  refine ⟨104105235921990258675931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 555227924917281379604965 104105235921990258675931)
                  ·
                    rfl

theorem cell22_912349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 4, 4].length) (baseStart_912349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_912349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_912349 prefixEnd_912349 := by exact prefixLift 912349
  have htrace : WordTrace (prefixWord ++ tailWord_912349) baseStart_912349 baseEnd_912349 := by
    simpa [prefixWord, tailWord_912349, baseEnd_912349] using wordTrace_append hprefix tailTrace_912349
  have hstable : (prefixWord ++ tailWord_912349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912349).length < 2 ^ (prefixWord ++ tailWord_912349).sum := by decide
  have hdescent : baseEnd_912349 < baseStart_912349 := by decide
  rcases family_descends (prefixWord ++ tailWord_912349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912360 : List Nat := [2, 1, 4, 1, 1, 1, 5, 7]
def baseStart_912360 : Nat := 118140960795 + 912360 * 2 ^ 59
def prefixEnd_912360 : Nat := 4983230072969 + 3 ^ 40 * 912360 * 2
def baseEnd_912360 : Nat := 34702163698974490444751

theorem tailTrace_912360 : CollatzResearch.WordTrace tailWord_912360 prefixEnd_912360 34702163698974490444751 := by
  unfold tailWord_912360
  simp only [CollatzResearch.WordTrace]
  refine ⟨16638251487341506763875267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22184335316455342351833689 16638251487341506763875267)
  ·
    refine ⟨24957377231012260145812901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16638251487341506763875267 24957377231012260145812901)
    ·
      refine ⟨4679508230814798777339919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24957377231012260145812901 4679508230814798777339919)
      ·
        refine ⟨7019262346222198166009879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4679508230814798777339919 7019262346222198166009879)
        ·
          refine ⟨10528893519333297249014819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7019262346222198166009879 10528893519333297249014819)
          ·
            refine ⟨15793340278999945873522229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10528893519333297249014819 15793340278999945873522229)
            ·
              refine ⟨1480625651156244925642709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15793340278999945873522229 1480625651156244925642709)
              ·
                refine ⟨34702163698974490444751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1480625651156244925642709 34702163698974490444751)
                ·
                  rfl

theorem cell22_912360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 7].length) (baseStart_912360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_912360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_912360 prefixEnd_912360 := by exact prefixLift 912360
  have htrace : WordTrace (prefixWord ++ tailWord_912360) baseStart_912360 baseEnd_912360 := by
    simpa [prefixWord, tailWord_912360, baseEnd_912360] using wordTrace_append hprefix tailTrace_912360
  have hstable : (prefixWord ++ tailWord_912360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912360).length < 2 ^ (prefixWord ++ tailWord_912360).sum := by decide
  have hdescent : baseEnd_912360 < baseStart_912360 := by decide
  rcases family_descends (prefixWord ++ tailWord_912360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912409 : List Nat := [1, 2, 1, 2, 1, 1, 6, 4, 1, 3]
def baseStart_912409 : Nat := 118140960795 + 912409 * 2 ^ 59
def prefixEnd_912409 : Nat := 4983230072969 + 3 ^ 40 * 912409 * 2
def baseEnd_912409 : Nat := 312336246992150619527609

theorem tailTrace_912409 : CollatzResearch.WordTrace tailWord_912409 prefixEnd_912409 312336246992150619527609 := by
  unfold tailWord_912409
  simp only [CollatzResearch.WordTrace]
  refine ⟨33278290151505494896284281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22185526767670329930856187 33278290151505494896284281)
  ·
    refine ⟨24958717613629121172213211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33278290151505494896284281 24958717613629121172213211)
    ·
      refine ⟨37438076420443681758319817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24958717613629121172213211 37438076420443681758319817)
      ·
        refine ⟨28078557315332761318739863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37438076420443681758319817 28078557315332761318739863)
        ·
          refine ⟨42117835972999141978109795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28078557315332761318739863 42117835972999141978109795)
          ·
            refine ⟨63176753959498712967164693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42117835972999141978109795 63176753959498712967164693)
            ·
              refine ⟨2961410341851502170335845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 63176753959498712967164693 2961410341851502170335845)
              ·
                refine ⟨555264439097156656937971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2961410341851502170335845 555264439097156656937971)
                ·
                  refine ⟨832896658645734985406957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 555264439097156656937971 832896658645734985406957)
                  ·
                    refine ⟨312336246992150619527609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 832896658645734985406957 312336246992150619527609)
                    ·
                      rfl

theorem cell22_912409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 4, 1, 3].length) (baseStart_912409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_912409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_912409 prefixEnd_912409 := by exact prefixLift 912409
  have htrace : WordTrace (prefixWord ++ tailWord_912409) baseStart_912409 baseEnd_912409 := by
    simpa [prefixWord, tailWord_912409, baseEnd_912409] using wordTrace_append hprefix tailTrace_912409
  have hstable : (prefixWord ++ tailWord_912409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912409).length < 2 ^ (prefixWord ++ tailWord_912409).sum := by decide
  have hdescent : baseEnd_912409 < baseStart_912409 := by decide
  rcases family_descends (prefixWord ++ tailWord_912409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912495 : List Nat := [1, 1, 2, 1, 3, 3, 1, 10]
def baseStart_912495 : Nat := 118140960795 + 912495 * 2 ^ 59
def prefixEnd_912495 : Nat := 4983230072969 + 3 ^ 40 * 912495 * 2
def baseEnd_912495 : Nat := 34707298505519451319705

theorem tailTrace_912495 : CollatzResearch.WordTrace tailWord_912495 prefixEnd_912495 34707298505519451319705 := by
  unfold tailWord_912495
  simp only [CollatzResearch.WordTrace]
  refine ⟨33281426829193931583914939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22187617886129287722609959 33281426829193931583914939)
  ·
    refine ⟨49922140243790897375872409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33281426829193931583914939 49922140243790897375872409)
    ·
      refine ⟨37441605182843173031904307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49922140243790897375872409 37441605182843173031904307)
      ·
        refine ⟨56162407774264759547856461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37441605182843173031904307 56162407774264759547856461)
        ·
          refine ⟨21060902915349284830446173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56162407774264759547856461 21060902915349284830446173)
          ·
            refine ⟨7897838593255981811417315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21060902915349284830446173 7897838593255981811417315)
            ·
              refine ⟨11846757889883972717125973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7897838593255981811417315 11846757889883972717125973)
              ·
                refine ⟨34707298505519451319705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 11846757889883972717125973 34707298505519451319705)
                ·
                  rfl

theorem cell22_912495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 10].length) (baseStart_912495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_912495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_912495 prefixEnd_912495 := by exact prefixLift 912495
  have htrace : WordTrace (prefixWord ++ tailWord_912495) baseStart_912495 baseEnd_912495 := by
    simpa [prefixWord, tailWord_912495, baseEnd_912495] using wordTrace_append hprefix tailTrace_912495
  have hstable : (prefixWord ++ tailWord_912495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912495).length < 2 ^ (prefixWord ++ tailWord_912495).sum := by decide
  have hdescent : baseEnd_912495 < baseStart_912495 := by decide
  rcases family_descends (prefixWord ++ tailWord_912495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912516 : List Nat := [2, 3, 2, 1, 2, 3, 2, 2, 2, 3]
def baseStart_912516 : Nat := 118140960795 + 912516 * 2 ^ 59
def prefixEnd_912516 : Nat := 4983230072969 + 3 ^ 40 * 912516 * 2
def baseEnd_912516 : Nat := 312372875278838007102281

theorem tailTrace_912516 : CollatzResearch.WordTrace tailWord_912516 prefixEnd_912516 312372875278838007102281 := by
  unfold tailWord_912516
  simp only [CollatzResearch.WordTrace]
  refine ⟨16641096381058926085214701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22188128508078568113619601 16641096381058926085214701)
  ·
    refine ⟨6240411142897097281955513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16641096381058926085214701 6240411142897097281955513)
    ·
      refine ⟨4680308357172822961466635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6240411142897097281955513 4680308357172822961466635)
      ·
        refine ⟨7020462535759234442199953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4680308357172822961466635 7020462535759234442199953)
        ·
          refine ⟨5265346901819425831649965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7020462535759234442199953 5265346901819425831649965)
          ·
            refine ⟨1974505088182284686868737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5265346901819425831649965 1974505088182284686868737)
            ·
              refine ⟨1480878816136713515151553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1974505088182284686868737 1480878816136713515151553)
              ·
                refine ⟨1110659112102535136363665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1480878816136713515151553 1110659112102535136363665)
                ·
                  refine ⟨832994334076901352272749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1110659112102535136363665 832994334076901352272749)
                  ·
                    refine ⟨312372875278838007102281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 832994334076901352272749 312372875278838007102281)
                    ·
                      rfl

theorem cell22_912516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_912516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_912516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_912516 prefixEnd_912516 := by exact prefixLift 912516
  have htrace : WordTrace (prefixWord ++ tailWord_912516) baseStart_912516 baseEnd_912516 := by
    simpa [prefixWord, tailWord_912516, baseEnd_912516] using wordTrace_append hprefix tailTrace_912516
  have hstable : (prefixWord ++ tailWord_912516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912516).length < 2 ^ (prefixWord ++ tailWord_912516).sum := by decide
  have hdescent : baseEnd_912516 < baseStart_912516 := by decide
  rcases family_descends (prefixWord ++ tailWord_912516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912544 : List Nat := [2, 1, 1, 4, 2, 1, 3, 2, 3, 3]
def baseStart_912544 : Nat := 118140960795 + 912544 * 2 ^ 59
def prefixEnd_912544 : Nat := 4983230072969 + 3 ^ 40 * 912544 * 2
def baseEnd_912544 : Nat := 312382460251055267402195

theorem tailTrace_912544 : CollatzResearch.WordTrace tailWord_912544 prefixEnd_912544 312382460251055267402195 := by
  unfold tailWord_912544
  simp only [CollatzResearch.WordTrace]
  refine ⟨16641607003008206476224343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22188809337344275301632457 16641607003008206476224343)
  ·
    refine ⟨24962410504512309714336515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16641607003008206476224343 24962410504512309714336515)
    ·
      refine ⟨37443615756768464571504773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24962410504512309714336515 37443615756768464571504773)
      ·
        refine ⟨7020677954394087107157145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37443615756768464571504773 7020677954394087107157145)
        ·
          refine ⟨5265508465795565330367859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7020677954394087107157145 5265508465795565330367859)
          ·
            refine ⟨7898262698693347995551789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5265508465795565330367859 7898262698693347995551789)
            ·
              refine ⟨2961848512010005498331921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7898262698693347995551789 2961848512010005498331921)
              ·
                refine ⟨2221386384007504123748941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2961848512010005498331921 2221386384007504123748941)
                ·
                  refine ⟨833019894002814046405853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2221386384007504123748941 833019894002814046405853)
                  ·
                    refine ⟨312382460251055267402195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 833019894002814046405853 312382460251055267402195)
                    ·
                      rfl

theorem cell22_912544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2, 3, 3].length) (baseStart_912544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_912544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_912544 prefixEnd_912544 := by exact prefixLift 912544
  have htrace : WordTrace (prefixWord ++ tailWord_912544) baseStart_912544 baseEnd_912544 := by
    simpa [prefixWord, tailWord_912544, baseEnd_912544] using wordTrace_append hprefix tailTrace_912544
  have hstable : (prefixWord ++ tailWord_912544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912544).length < 2 ^ (prefixWord ++ tailWord_912544).sum := by decide
  have hdescent : baseEnd_912544 < baseStart_912544 := by decide
  rcases family_descends (prefixWord ++ tailWord_912544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912546 : List Nat := [3, 3, 1, 3, 2, 1, 3, 6]
def baseStart_912546 : Nat := 118140960795 + 912546 * 2 ^ 59
def prefixEnd_912546 : Nat := 4983230072969 + 3 ^ 40 * 912546 * 2
def baseEnd_912546 : Nat := 34709238321325325428021

theorem tailTrace_912546 : CollatzResearch.WordTrace tailWord_912546 prefixEnd_912546 34709238321325325428021 := by
  unfold tailWord_912546
  simp only [CollatzResearch.WordTrace]
  refine ⟨8320821738002291823505373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22188857968006111529347661 8320821738002291823505373)
  ·
    refine ⟨3120308151750859433814515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8320821738002291823505373 3120308151750859433814515)
    ·
      refine ⟨4680462227626289150721773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3120308151750859433814515 4680462227626289150721773)
      ·
        refine ⟨1755173335359858431520665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4680462227626289150721773 1755173335359858431520665)
        ·
          refine ⟨1316380001519893823640499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1755173335359858431520665 1316380001519893823640499)
          ·
            refine ⟨1974570002279840735460749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1316380001519893823640499 1974570002279840735460749)
            ·
              refine ⟨740463750854940275797781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1974570002279840735460749 740463750854940275797781)
              ·
                refine ⟨34709238321325325428021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 740463750854940275797781 34709238321325325428021)
                ·
                  rfl

theorem cell22_912546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 6].length) (baseStart_912546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_912546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_912546 prefixEnd_912546 := by exact prefixLift 912546
  have htrace : WordTrace (prefixWord ++ tailWord_912546) baseStart_912546 baseEnd_912546 := by
    simpa [prefixWord, tailWord_912546, baseEnd_912546] using wordTrace_append hprefix tailTrace_912546
  have hstable : (prefixWord ++ tailWord_912546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912546).length < 2 ^ (prefixWord ++ tailWord_912546).sum := by decide
  have hdescent : baseEnd_912546 < baseStart_912546 := by decide
  rcases family_descends (prefixWord ++ tailWord_912546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912574 : List Nat := [4, 2, 1, 1, 3, 2, 1, 1, 7]
def baseStart_912574 : Nat := 118140960795 + 912574 * 2 ^ 59
def prefixEnd_912574 : Nat := 4983230072969 + 3 ^ 40 * 912574 * 2
def baseEnd_912574 : Nat := 104130909954715063050701

theorem tailTrace_912574 : CollatzResearch.WordTrace tailWord_912574 prefixEnd_912574 104130909954715063050701 := by
  unfold tailWord_912574
  simp only [CollatzResearch.WordTrace]
  refine ⟨4160538524488466009505097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22189538797271818717360517 4160538524488466009505097)
  ·
    refine ⟨3120403893366349507128823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4160538524488466009505097 3120403893366349507128823)
    ·
      refine ⟨4680605840049524260693235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3120403893366349507128823 4680605840049524260693235)
      ·
        refine ⟨7020908760074286391039853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4680605840049524260693235 7020908760074286391039853)
        ·
          refine ⟨2632840785027857396639945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7020908760074286391039853 2632840785027857396639945)
          ·
            refine ⟨1974630588770893047479959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2632840785027857396639945 1974630588770893047479959)
            ·
              refine ⟨2961945883156339571219939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1974630588770893047479959 2961945883156339571219939)
              ·
                refine ⟨4442918824734509356829909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2961945883156339571219939 4442918824734509356829909)
                ·
                  refine ⟨104130909954715063050701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4442918824734509356829909 104130909954715063050701)
                  ·
                    rfl

theorem cell22_912574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_912574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_912574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_912574 prefixEnd_912574 := by exact prefixLift 912574
  have htrace : WordTrace (prefixWord ++ tailWord_912574) baseStart_912574 baseEnd_912574 := by
    simpa [prefixWord, tailWord_912574, baseEnd_912574] using wordTrace_append hprefix tailTrace_912574
  have hstable : (prefixWord ++ tailWord_912574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912574).length < 2 ^ (prefixWord ++ tailWord_912574).sum := by decide
  have hdescent : baseEnd_912574 < baseStart_912574 := by decide
  rcases family_descends (prefixWord ++ tailWord_912574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912587 : List Nat := [1, 1, 1, 1, 3, 2, 2, 4, 3, 4]
def baseStart_912587 : Nat := 118140960795 + 912587 * 2 ^ 59
def prefixEnd_912587 : Nat := 4983230072969 + 3 ^ 40 * 912587 * 2
def baseEnd_912587 : Nat := 312397180029817488577063

theorem tailTrace_912587 : CollatzResearch.WordTrace tailWord_912587 prefixEnd_912587 312397180029817488577063 := by
  unfold tailWord_912587
  simp only [CollatzResearch.WordTrace]
  refine ⟨33284782344860631296264015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22189854896573754197509343 33284782344860631296264015)
  ·
    refine ⟨49927173517290946944396023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33284782344860631296264015 49927173517290946944396023)
    ·
      refine ⟨74890760275936420416594035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49927173517290946944396023 74890760275936420416594035)
      ·
        refine ⟨112336140413904630624891053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74890760275936420416594035 112336140413904630624891053)
        ·
          refine ⟨42126052655214236484334145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112336140413904630624891053 42126052655214236484334145)
          ·
            refine ⟨31594539491410677363250609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42126052655214236484334145 31594539491410677363250609)
            ·
              refine ⟨23695904618558008022437957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31594539491410677363250609 23695904618558008022437957)
              ·
                refine ⟨4442982115979626504207117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23695904618558008022437957 4442982115979626504207117)
                ·
                  refine ⟨1666118293492359939077669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4442982115979626504207117 1666118293492359939077669)
                  ·
                    refine ⟨312397180029817488577063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1666118293492359939077669 312397180029817488577063)
                    ·
                      rfl

theorem cell22_912587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 3, 4].length) (baseStart_912587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_912587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_912587 prefixEnd_912587 := by exact prefixLift 912587
  have htrace : WordTrace (prefixWord ++ tailWord_912587) baseStart_912587 baseEnd_912587 := by
    simpa [prefixWord, tailWord_912587, baseEnd_912587] using wordTrace_append hprefix tailTrace_912587
  have hstable : (prefixWord ++ tailWord_912587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912587).length < 2 ^ (prefixWord ++ tailWord_912587).sum := by decide
  have hdescent : baseEnd_912587 < baseStart_912587 := by decide
  rcases family_descends (prefixWord ++ tailWord_912587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912621 : List Nat := [1, 5, 1, 2, 2, 1, 2, 3, 1, 4]
def baseStart_912621 : Nat := 118140960795 + 912621 * 2 ^ 59
def prefixEnd_912621 : Nat := 4983230072969 + 3 ^ 40 * 912621 * 2
def baseEnd_912621 : Nat := 312408818924652733226959

theorem tailTrace_912621 : CollatzResearch.WordTrace tailWord_912621 prefixEnd_912621 312408818924652733226959 := by
  unfold tailWord_912621
  simp only [CollatzResearch.WordTrace]
  refine ⟨33286022426737455103001717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22190681617824970068667811 33286022426737455103001717)
  ·
    refine ⟨3120564602506636415906411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33286022426737455103001717 3120564602506636415906411)
    ·
      refine ⟨4680846903759954623859617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3120564602506636415906411 4680846903759954623859617)
      ·
        refine ⟨3510635177819965967894713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4680846903759954623859617 3510635177819965967894713)
        ·
          refine ⟨2632976383364974475921035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3510635177819965967894713 2632976383364974475921035)
          ·
            refine ⟨3949464575047461713881553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2632976383364974475921035 3949464575047461713881553)
            ·
              refine ⟨2962098431285596285411165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3949464575047461713881553 2962098431285596285411165)
              ·
                refine ⟨1110786911732098607029187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2962098431285596285411165 1110786911732098607029187)
                ·
                  refine ⟨1666180367598147910543781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1110786911732098607029187 1666180367598147910543781)
                  ·
                    refine ⟨312408818924652733226959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1666180367598147910543781 312408818924652733226959)
                    ·
                      rfl

theorem cell22_912621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_912621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_912621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_912621 prefixEnd_912621 := by exact prefixLift 912621
  have htrace : WordTrace (prefixWord ++ tailWord_912621) baseStart_912621 baseEnd_912621 := by
    simpa [prefixWord, tailWord_912621, baseEnd_912621] using wordTrace_append hprefix tailTrace_912621
  have hstable : (prefixWord ++ tailWord_912621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912621).length < 2 ^ (prefixWord ++ tailWord_912621).sum := by decide
  have hdescent : baseEnd_912621 < baseStart_912621 := by decide
  rcases family_descends (prefixWord ++ tailWord_912621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912634 : List Nat := [3, 1, 1, 1, 1, 4, 1, 3, 4, 3]
def baseStart_912634 : Nat := 118140960795 + 912634 * 2 ^ 59
def prefixEnd_912634 : Nat := 4983230072969 + 3 ^ 40 * 912634 * 2
def baseEnd_912634 : Nat := 312413269090325032651919

theorem tailTrace_912634 : CollatzResearch.WordTrace tailWord_912634 prefixEnd_912634 312413269090325032651919 := by
  unfold tailWord_912634
  simp only [CollatzResearch.WordTrace]
  refine ⟨8321624143922589580806239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22190997717126905548816637 8321624143922589580806239)
  ·
    refine ⟨12482436215883884371209359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8321624143922589580806239 12482436215883884371209359)
    ·
      refine ⟨18723654323825826556814039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12482436215883884371209359 18723654323825826556814039)
      ·
        refine ⟨28085481485738739835221059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18723654323825826556814039 28085481485738739835221059)
        ·
          refine ⟨42128222228608109752831589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28085481485738739835221059 42128222228608109752831589)
          ·
            refine ⟨7899041667864020578655923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42128222228608109752831589 7899041667864020578655923)
            ·
              refine ⟨11848562501796030867983885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7899041667864020578655923 11848562501796030867983885)
              ·
                refine ⟨4443210938173511575493957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11848562501796030867983885 4443210938173511575493957)
                ·
                  refine ⟨833102050907533420405117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4443210938173511575493957 833102050907533420405117)
                  ·
                    refine ⟨312413269090325032651919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 833102050907533420405117 312413269090325032651919)
                    ·
                      rfl

theorem cell22_912634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 4, 3].length) (baseStart_912634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_912634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_912634 prefixEnd_912634 := by exact prefixLift 912634
  have htrace : WordTrace (prefixWord ++ tailWord_912634) baseStart_912634 baseEnd_912634 := by
    simpa [prefixWord, tailWord_912634, baseEnd_912634] using wordTrace_append hprefix tailTrace_912634
  have hstable : (prefixWord ++ tailWord_912634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912634).length < 2 ^ (prefixWord ++ tailWord_912634).sum := by decide
  have hdescent : baseEnd_912634 < baseStart_912634 := by decide
  rcases family_descends (prefixWord ++ tailWord_912634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912636 : List Nat := [2, 2, 2, 1, 5, 2, 1, 1, 6]
def baseStart_912636 : Nat := 118140960795 + 912636 * 2 ^ 59
def prefixEnd_912636 : Nat := 4983230072969 + 3 ^ 40 * 912636 * 2
def baseEnd_912636 : Nat := 104137984577065898033971

theorem tailTrace_912636 : CollatzResearch.WordTrace tailWord_912636 prefixEnd_912636 104137984577065898033971 := by
  unfold tailWord_912636
  simp only [CollatzResearch.WordTrace]
  refine ⟨16643284760841556332398881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22191046347788741776531841 16643284760841556332398881)
  ·
    refine ⟨12482463570631167249299161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16643284760841556332398881 12482463570631167249299161)
    ·
      refine ⟨9361847677973375436974371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12482463570631167249299161 9361847677973375436974371)
      ·
        refine ⟨14042771516960063155461557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9361847677973375436974371 14042771516960063155461557)
        ·
          refine ⟨1316509829715005920824521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14042771516960063155461557 1316509829715005920824521)
          ·
            refine ⟨987382372286254440618391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1316509829715005920824521 987382372286254440618391)
            ·
              refine ⟨1481073558429381660927587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 987382372286254440618391 1481073558429381660927587)
              ·
                refine ⟨2221610337644072491391381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1481073558429381660927587 2221610337644072491391381)
                ·
                  refine ⟨104137984577065898033971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2221610337644072491391381 104137984577065898033971)
                  ·
                    rfl

theorem cell22_912636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 1, 6].length) (baseStart_912636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_912636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_912636 prefixEnd_912636 := by exact prefixLift 912636
  have htrace : WordTrace (prefixWord ++ tailWord_912636) baseStart_912636 baseEnd_912636 := by
    simpa [prefixWord, tailWord_912636, baseEnd_912636] using wordTrace_append hprefix tailTrace_912636
  have hstable : (prefixWord ++ tailWord_912636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912636).length < 2 ^ (prefixWord ++ tailWord_912636).sum := by decide
  have hdescent : baseEnd_912636 < baseStart_912636 := by decide
  rcases family_descends (prefixWord ++ tailWord_912636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912651 : List Nat := [1, 1, 1, 1, 5, 4, 1, 3, 2, 3]
def baseStart_912651 : Nat := 118140960795 + 912651 * 2 ^ 59
def prefixEnd_912651 : Nat := 4983230072969 + 3 ^ 40 * 912651 * 2
def baseEnd_912651 : Nat := 312419088537742654976867

theorem tailTrace_912651 : CollatzResearch.WordTrace tailWord_912651 prefixEnd_912651 312419088537742654976867 := by
  unfold tailWord_912651
  simp only [CollatzResearch.WordTrace]
  refine ⟨33287116616628770226593807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22191411077752513484395871 33287116616628770226593807)
  ·
    refine ⟨49930674924943155339890711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33287116616628770226593807 49930674924943155339890711)
    ·
      refine ⟨74896012387414733009836067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49930674924943155339890711 74896012387414733009836067)
      ·
        refine ⟨112344018581122099514754101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74896012387414733009836067 112344018581122099514754101)
        ·
          refine ⟨10532251741980196829508197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112344018581122099514754101 10532251741980196829508197)
          ·
            refine ⟨1974797201621286905532787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10532251741980196829508197 1974797201621286905532787)
            ·
              refine ⟨2962195802431930358299181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1974797201621286905532787 2962195802431930358299181)
              ·
                refine ⟨1110823425911973884362193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2962195802431930358299181 1110823425911973884362193)
                ·
                  refine ⟨833117569433980413271645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1110823425911973884362193 833117569433980413271645)
                  ·
                    refine ⟨312419088537742654976867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 833117569433980413271645 312419088537742654976867)
                    ·
                      rfl

theorem cell22_912651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 3, 2, 3].length) (baseStart_912651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_912651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_912651 prefixEnd_912651 := by exact prefixLift 912651
  have htrace : WordTrace (prefixWord ++ tailWord_912651) baseStart_912651 baseEnd_912651 := by
    simpa [prefixWord, tailWord_912651, baseEnd_912651] using wordTrace_append hprefix tailTrace_912651
  have hstable : (prefixWord ++ tailWord_912651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912651).length < 2 ^ (prefixWord ++ tailWord_912651).sum := by decide
  have hdescent : baseEnd_912651 < baseStart_912651 := by decide
  rcases family_descends (prefixWord ++ tailWord_912651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912666 : List Nat := [3, 1, 1, 3, 3, 2, 2, 1, 2, 4]
def baseStart_912666 : Nat := 118140960795 + 912666 * 2 ^ 59
def prefixEnd_912666 : Nat := 4983230072969 + 3 ^ 40 * 912666 * 2
def baseEnd_912666 : Nat := 312424223344287615851821

theorem tailTrace_912666 : CollatzResearch.WordTrace tailWord_912666 prefixEnd_912666 312424223344287615851821 := by
  unfold tailWord_912666
  simp only [CollatzResearch.WordTrace]
  refine ⟨8321915927893606947097463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22191775807716285192259901 8321915927893606947097463)
  ·
    refine ⟨12482873891840410420646195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8321915927893606947097463 12482873891840410420646195)
    ·
      refine ⟨18724310837760615630969293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12482873891840410420646195 18724310837760615630969293)
      ·
        refine ⟨7021616564160230861613485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18724310837760615630969293 7021616564160230861613485)
        ·
          refine ⟨2633106211560086573105057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7021616564160230861613485 2633106211560086573105057)
          ·
            refine ⟨1974829658670064929828793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2633106211560086573105057 1974829658670064929828793)
            ·
              refine ⟨1481122244002548697371595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1974829658670064929828793 1481122244002548697371595)
              ·
                refine ⟨2221683366003823046057393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1481122244002548697371595 2221683366003823046057393)
                ·
                  refine ⟨1666262524502867284543045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2221683366003823046057393 1666262524502867284543045)
                  ·
                    refine ⟨312424223344287615851821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1666262524502867284543045 312424223344287615851821)
                    ·
                      rfl

theorem cell22_912666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 1, 2, 4].length) (baseStart_912666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_912666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_912666 prefixEnd_912666 := by exact prefixLift 912666
  have htrace : WordTrace (prefixWord ++ tailWord_912666) baseStart_912666 baseEnd_912666 := by
    simpa [prefixWord, tailWord_912666, baseEnd_912666] using wordTrace_append hprefix tailTrace_912666
  have hstable : (prefixWord ++ tailWord_912666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912666).length < 2 ^ (prefixWord ++ tailWord_912666).sum := by decide
  have hdescent : baseEnd_912666 < baseStart_912666 := by decide
  rcases family_descends (prefixWord ++ tailWord_912666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912685 : List Nat := [1, 5, 3, 1, 1, 2, 2, 2, 2, 3]
def baseStart_912685 : Nat := 118140960795 + 912685 * 2 ^ 59
def prefixEnd_912685 : Nat := 4983230072969 + 3 ^ 40 * 912685 * 2
def baseEnd_912685 : Nat := 312430727432577899626763

theorem tailTrace_912685 : CollatzResearch.WordTrace tailWord_912685 prefixEnd_912685 312430727432577899626763 := by
  unfold tailWord_912685
  simp only [CollatzResearch.WordTrace]
  refine ⟨33288356698505594033331509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22192237799003729355554339 33288356698505594033331509)
  ·
    refine ⟨3120783440484899440624829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33288356698505594033331509 3120783440484899440624829)
    ·
      refine ⟨1170293790181837290234311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3120783440484899440624829 1170293790181837290234311)
      ·
        refine ⟨1755440685272755935351467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1170293790181837290234311 1755440685272755935351467)
        ·
          refine ⟨2633161027909133903027201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1755440685272755935351467 2633161027909133903027201)
          ·
            refine ⟨1974870770931850427270401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2633161027909133903027201 1974870770931850427270401)
            ·
              refine ⟨1481153078198887820452801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1974870770931850427270401 1481153078198887820452801)
              ·
                refine ⟨1110864808649165865339601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1481153078198887820452801 1110864808649165865339601)
                ·
                  refine ⟨833148606486874399004701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1110864808649165865339601 833148606486874399004701)
                  ·
                    refine ⟨312430727432577899626763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 833148606486874399004701 312430727432577899626763)
                    ·
                      rfl

theorem cell22_912685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_912685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_912685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_912685 prefixEnd_912685 := by exact prefixLift 912685
  have htrace : WordTrace (prefixWord ++ tailWord_912685) baseStart_912685 baseEnd_912685 := by
    simpa [prefixWord, tailWord_912685, baseEnd_912685] using wordTrace_append hprefix tailTrace_912685
  have hstable : (prefixWord ++ tailWord_912685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912685).length < 2 ^ (prefixWord ++ tailWord_912685).sum := by decide
  have hdescent : baseEnd_912685 < baseStart_912685 := by decide
  rcases family_descends (prefixWord ++ tailWord_912685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912717 : List Nat := [1, 6, 1, 3, 2, 1, 1, 1, 2, 4]
def baseStart_912717 : Nat := 118140960795 + 912717 * 2 ^ 59
def prefixEnd_912717 : Nat := 4983230072969 + 3 ^ 40 * 912717 * 2
def baseEnd_912717 : Nat := 312441681686540482826665

theorem tailTrace_912717 : CollatzResearch.WordTrace tailWord_912717 prefixEnd_912717 312441681686540482826665 := by
  unfold tailWord_912717
  simp only [CollatzResearch.WordTrace]
  refine ⟨33289523834389663498496405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22193015889593108998997603 33289523834389663498496405)
  ·
    refine ⟨1560446429737015476492019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 33289523834389663498496405 1560446429737015476492019)
    ·
      refine ⟨2340669644605523214738029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1560446429737015476492019 2340669644605523214738029)
      ·
        refine ⟨877751116727071205526761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2340669644605523214738029 877751116727071205526761)
        ·
          refine ⟨658313337545303404145071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 877751116727071205526761 658313337545303404145071)
          ·
            refine ⟨987470006317955106217607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 658313337545303404145071 987470006317955106217607)
            ·
              refine ⟨1481205009476932659326411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 987470006317955106217607 1481205009476932659326411)
              ·
                refine ⟨2221807514215398988989617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1481205009476932659326411 2221807514215398988989617)
                ·
                  refine ⟨1666355635661549241742213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2221807514215398988989617 1666355635661549241742213)
                  ·
                    refine ⟨312441681686540482826665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1666355635661549241742213 312441681686540482826665)
                    ·
                      rfl

theorem cell22_912717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_912717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_912717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_912717 prefixEnd_912717 := by exact prefixLift 912717
  have htrace : WordTrace (prefixWord ++ tailWord_912717) baseStart_912717 baseEnd_912717 := by
    simpa [prefixWord, tailWord_912717, baseEnd_912717] using wordTrace_append hprefix tailTrace_912717
  have hstable : (prefixWord ++ tailWord_912717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912717).length < 2 ^ (prefixWord ++ tailWord_912717).sum := by decide
  have hdescent : baseEnd_912717 < baseStart_912717 := by decide
  rcases family_descends (prefixWord ++ tailWord_912717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912724 : List Nat := [2, 4, 1, 1, 2, 1, 1, 2, 1, 7]
def baseStart_912724 : Nat := 118140960795 + 912724 * 2 ^ 59
def prefixEnd_912724 : Nat := 4983230072969 + 3 ^ 40 * 912724 * 2
def baseEnd_912724 : Nat := 312444077929594797901643

theorem tailTrace_912724 : CollatzResearch.WordTrace tailWord_912724 prefixEnd_912724 312444077929594797901643 := by
  unfold tailWord_912724
  simp only [CollatzResearch.WordTrace]
  refine ⟨16644889572682151847000613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22193186096909535796000817 16644889572682151847000613)
  ·
    refine ⟨3120916794877903471312615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16644889572682151847000613 3120916794877903471312615)
    ·
      refine ⟨4681375192316855206968923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3120916794877903471312615 4681375192316855206968923)
      ·
        refine ⟨7022062788475282810453385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4681375192316855206968923 7022062788475282810453385)
        ·
          refine ⟨5266547091356462107840039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7022062788475282810453385 5266547091356462107840039)
          ·
            refine ⟨7899820637034693161760059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5266547091356462107840039 7899820637034693161760059)
            ·
              refine ⟨11849730955552039742640089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7899820637034693161760059 11849730955552039742640089)
              ·
                refine ⟨8887298216664029806980067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11849730955552039742640089 8887298216664029806980067)
                ·
                  refine ⟨13330947324996044710470101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8887298216664029806980067 13330947324996044710470101)
                  ·
                    refine ⟨312444077929594797901643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13330947324996044710470101 312444077929594797901643)
                    ·
                      rfl

theorem cell22_912724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_912724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_912724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_912724 prefixEnd_912724 := by exact prefixLift 912724
  have htrace : WordTrace (prefixWord ++ tailWord_912724) baseStart_912724 baseEnd_912724 := by
    simpa [prefixWord, tailWord_912724, baseEnd_912724] using wordTrace_append hprefix tailTrace_912724
  have hstable : (prefixWord ++ tailWord_912724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912724).length < 2 ^ (prefixWord ++ tailWord_912724).sum := by decide
  have hdescent : baseEnd_912724 < baseStart_912724 := by decide
  rcases family_descends (prefixWord ++ tailWord_912724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912743 : List Nat := [1, 1, 5, 1, 4, 2, 1, 2, 5]
def baseStart_912743 : Nat := 118140960795 + 912743 * 2 ^ 59
def prefixEnd_912743 : Nat := 4983230072969 + 3 ^ 40 * 912743 * 2
def baseEnd_912743 : Nat := 104150194005961693892195

theorem tailTrace_912743 : CollatzResearch.WordTrace tailWord_912743 prefixEnd_912743 104150194005961693892195 := by
  unfold tailWord_912743
  simp only [CollatzResearch.WordTrace]
  refine ⟨33290472132295469938942883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22193648088196979959295255 33290472132295469938942883)
  ·
    refine ⟨49935708198443204908414325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33290472132295469938942883 49935708198443204908414325)
    ·
      refine ⟨4681472643604050460163843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49935708198443204908414325 4681472643604050460163843)
      ·
        refine ⟨7022208965406075690245765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4681472643604050460163843 7022208965406075690245765)
        ·
          refine ⟨1316664181013639191921081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7022208965406075690245765 1316664181013639191921081)
          ·
            refine ⟨987498135760229393940811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1316664181013639191921081 987498135760229393940811)
            ·
              refine ⟨1481247203640344090911217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 987498135760229393940811 1481247203640344090911217)
              ·
                refine ⟨1110935402730258068183413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1481247203640344090911217 1110935402730258068183413)
                ·
                  refine ⟨104150194005961693892195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1110935402730258068183413 104150194005961693892195)
                  ·
                    rfl

theorem cell22_912743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 2, 5].length) (baseStart_912743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_912743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_912743 prefixEnd_912743 := by exact prefixLift 912743
  have htrace : WordTrace (prefixWord ++ tailWord_912743) baseStart_912743 baseEnd_912743 := by
    simpa [prefixWord, tailWord_912743, baseEnd_912743] using wordTrace_append hprefix tailTrace_912743
  have hstable : (prefixWord ++ tailWord_912743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912743).length < 2 ^ (prefixWord ++ tailWord_912743).sum := by decide
  have hdescent : baseEnd_912743 < baseStart_912743 := by decide
  rcases family_descends (prefixWord ++ tailWord_912743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912799 : List Nat := [1, 1, 2, 5, 1, 2, 10]
def baseStart_912799 : Nat := 118140960795 + 912799 * 2 ^ 59
def prefixEnd_912799 : Nat := 4983230072969 + 3 ^ 40 * 912799 * 2
def baseEnd_912799 : Nat := 11572953776382207491719

theorem tailTrace_912799 : CollatzResearch.WordTrace tailWord_912799 prefixEnd_912799 11572953776382207491719 := by
  unfold tailWord_912799
  simp only [CollatzResearch.WordTrace]
  refine ⟨33292514620092591502981451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22195009746728394335320967 33292514620092591502981451)
  ·
    refine ⟨49938771930138887254472177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33292514620092591502981451 49938771930138887254472177)
    ·
      refine ⟨37454078947604165440854133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49938771930138887254472177 37454078947604165440854133)
      ·
        refine ⟨3511319901337890510080075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37454078947604165440854133 3511319901337890510080075)
        ·
          refine ⟨5266979852006835765120113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3511319901337890510080075 5266979852006835765120113)
          ·
            refine ⟨3950234889005126823840085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5266979852006835765120113 3950234889005126823840085)
            ·
              refine ⟨11572953776382207491719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3950234889005126823840085 11572953776382207491719)
              ·
                rfl

theorem cell22_912799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 10].length) (baseStart_912799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_912799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_912799 prefixEnd_912799 := by exact prefixLift 912799
  have htrace : WordTrace (prefixWord ++ tailWord_912799) baseStart_912799 baseEnd_912799 := by
    simpa [prefixWord, tailWord_912799, baseEnd_912799] using wordTrace_append hprefix tailTrace_912799
  have hstable : (prefixWord ++ tailWord_912799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912799).length < 2 ^ (prefixWord ++ tailWord_912799).sum := by decide
  have hdescent : baseEnd_912799 < baseStart_912799 := by decide
  rcases family_descends (prefixWord ++ tailWord_912799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912831 : List Nat := [1, 1, 2, 2, 2, 1, 1, 6, 3, 3]
def baseStart_912831 : Nat := 118140960795 + 912831 * 2 ^ 59
def prefixEnd_912831 : Nat := 4983230072969 + 3 ^ 40 * 912831 * 2
def baseEnd_912831 : Nat := 312480706216282185476315

theorem tailTrace_912831 : CollatzResearch.WordTrace tailWord_912831 prefixEnd_912831 312480706216282185476315 := by
  unfold tailWord_912831
  simp only [CollatzResearch.WordTrace]
  refine ⟨33293681755976660968146347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22195787837317773978764231 33293681755976660968146347)
  ·
    refine ⟨49940522633964991452219521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33293681755976660968146347 49940522633964991452219521)
    ·
      refine ⟨37455391975473743589164641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49940522633964991452219521 37455391975473743589164641)
      ·
        refine ⟨28091543981605307691873481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37455391975473743589164641 28091543981605307691873481)
        ·
          refine ⟨21068657986203980768905111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28091543981605307691873481 21068657986203980768905111)
          ·
            refine ⟨31602986979305971153357667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21068657986203980768905111 31602986979305971153357667)
            ·
              refine ⟨47404480468958956730036501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31602986979305971153357667 47404480468958956730036501)
              ·
                refine ⟨2222085021982451096720461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47404480468958956730036501 2222085021982451096720461)
                ·
                  refine ⟨833281883243419161270173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2222085021982451096720461 833281883243419161270173)
                  ·
                    refine ⟨312480706216282185476315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 833281883243419161270173 312480706216282185476315)
                    ·
                      rfl

theorem cell22_912831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6, 3, 3].length) (baseStart_912831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_912831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_912831 prefixEnd_912831 := by exact prefixLift 912831
  have htrace : WordTrace (prefixWord ++ tailWord_912831) baseStart_912831 baseEnd_912831 := by
    simpa [prefixWord, tailWord_912831, baseEnd_912831] using wordTrace_append hprefix tailTrace_912831
  have hstable : (prefixWord ++ tailWord_912831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912831).length < 2 ^ (prefixWord ++ tailWord_912831).sum := by decide
  have hdescent : baseEnd_912831 < baseStart_912831 := by decide
  rcases family_descends (prefixWord ++ tailWord_912831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912859 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 8, 5]
def baseStart_912859 : Nat := 118140960795 + 912859 * 2 ^ 59
def prefixEnd_912859 : Nat := 4983230072969 + 3 ^ 40 * 912859 * 2
def baseEnd_912859 : Nat := 312490291188499445776229

theorem tailTrace_912859 : CollatzResearch.WordTrace tailWord_912859 prefixEnd_912859 312490291188499445776229 := by
  unfold tailWord_912859
  simp only [CollatzResearch.WordTrace]
  refine ⟨33294702999875221750165631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22196468666583481166777087 33294702999875221750165631)
  ·
    refine ⟨49942054499812832625248447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33294702999875221750165631 49942054499812832625248447)
    ·
      refine ⟨74913081749719248937872671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49942054499812832625248447 74913081749719248937872671)
      ·
        refine ⟨112369622624578873406809007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74913081749719248937872671 112369622624578873406809007)
        ·
          refine ⟨168554433936868310110213511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112369622624578873406809007 168554433936868310110213511)
          ·
            refine ⟨252831650905302465165320267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168554433936868310110213511 252831650905302465165320267)
            ·
              refine ⟨379247476357953697747980401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252831650905302465165320267 379247476357953697747980401)
              ·
                refine ⟨284435607268465273310985301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 379247476357953697747980401 284435607268465273310985301)
                ·
                  refine ⟨3333229772677327421613109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 284435607268465273310985301 3333229772677327421613109)
                  ·
                    refine ⟨312490291188499445776229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3333229772677327421613109 312490291188499445776229)
                    ·
                      rfl

theorem cell22_912859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8, 5].length) (baseStart_912859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_912859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_912859 prefixEnd_912859 := by exact prefixLift 912859
  have htrace : WordTrace (prefixWord ++ tailWord_912859) baseStart_912859 baseEnd_912859 := by
    simpa [prefixWord, tailWord_912859, baseEnd_912859] using wordTrace_append hprefix tailTrace_912859
  have hstable : (prefixWord ++ tailWord_912859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912859).length < 2 ^ (prefixWord ++ tailWord_912859).sum := by decide
  have hdescent : baseEnd_912859 < baseStart_912859 := by decide
  rcases family_descends (prefixWord ++ tailWord_912859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912865 : List Nat := [1, 2, 3, 1, 2, 4, 1, 4, 1, 3]
def baseStart_912865 : Nat := 118140960795 + 912865 * 2 ^ 59
def prefixEnd_912865 : Nat := 4983230072969 + 3 ^ 40 * 912865 * 2
def baseEnd_912865 : Nat := 312492345111117430126211

theorem tailTrace_912865 : CollatzResearch.WordTrace tailWord_912865 prefixEnd_912865 312492345111117430126211 := by
  unfold tailWord_912865
  simp only [CollatzResearch.WordTrace]
  refine ⟨33294921837853484774884049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22196614558568989849922699 33294921837853484774884049)
  ·
    refine ⟨24971191378390113581163037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33294921837853484774884049 24971191378390113581163037)
    ·
      refine ⟨9364196766896292592936139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24971191378390113581163037 9364196766896292592936139)
      ·
        refine ⟨14046295150344438889404209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9364196766896292592936139 14046295150344438889404209)
        ·
          refine ⟨10534721362758329167053157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14046295150344438889404209 10534721362758329167053157)
          ·
            refine ⟨1975260255517186718822467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10534721362758329167053157 1975260255517186718822467)
            ·
              refine ⟨2962890383275780078233701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1975260255517186718822467 2962890383275780078233701)
              ·
                refine ⟨555541946864208764668819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2962890383275780078233701 555541946864208764668819)
                ·
                  refine ⟨833312920296313147003229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 555541946864208764668819 833312920296313147003229)
                  ·
                    refine ⟨312492345111117430126211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 833312920296313147003229 312492345111117430126211)
                    ·
                      rfl

theorem cell22_912865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 4, 1, 3].length) (baseStart_912865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_912865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_912865 prefixEnd_912865 := by exact prefixLift 912865
  have htrace : WordTrace (prefixWord ++ tailWord_912865) baseStart_912865 baseEnd_912865 := by
    simpa [prefixWord, tailWord_912865, baseEnd_912865] using wordTrace_append hprefix tailTrace_912865
  have hstable : (prefixWord ++ tailWord_912865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912865).length < 2 ^ (prefixWord ++ tailWord_912865).sum := by decide
  have hdescent : baseEnd_912865 < baseStart_912865 := by decide
  rcases family_descends (prefixWord ++ tailWord_912865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912951 : List Nat := [1, 1, 3, 1, 2, 5, 1, 8]
def baseStart_912951 : Nat := 118140960795 + 912951 * 2 ^ 59
def prefixEnd_912951 : Nat := 4983230072969 + 3 ^ 40 * 912951 * 2
def baseEnd_912951 : Nat := 34724642740960208052883

theorem tailTrace_912951 : CollatzResearch.WordTrace tailWord_912951 prefixEnd_912951 34724642740960208052883 := by
  unfold tailWord_912951
  simp only [CollatzResearch.WordTrace]
  refine ⟨33298058515541921462514707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22198705677027947641676471 33298058515541921462514707)
  ·
    refine ⟨49947087773312882193772061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33298058515541921462514707 49947087773312882193772061)
    ·
      refine ⟨18730157914992330822664523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49947087773312882193772061 18730157914992330822664523)
      ·
        refine ⟨28095236872488496233996785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18730157914992330822664523 28095236872488496233996785)
        ·
          refine ⟨21071427654366372175497589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28095236872488496233996785 21071427654366372175497589)
          ·
            refine ⟨1975446342596847391452899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21071427654366372175497589 1975446342596847391452899)
            ·
              refine ⟨2963169513895271087179349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1975446342596847391452899 2963169513895271087179349)
              ·
                refine ⟨34724642740960208052883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2963169513895271087179349 34724642740960208052883)
                ·
                  rfl

theorem cell22_912951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 8].length) (baseStart_912951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_912951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_912951 prefixEnd_912951 := by exact prefixLift 912951
  have htrace : WordTrace (prefixWord ++ tailWord_912951) baseStart_912951 baseEnd_912951 := by
    simpa [prefixWord, tailWord_912951, baseEnd_912951] using wordTrace_append hprefix tailTrace_912951
  have hstable : (prefixWord ++ tailWord_912951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912951).length < 2 ^ (prefixWord ++ tailWord_912951).sum := by decide
  have hdescent : baseEnd_912951 < baseStart_912951 := by decide
  rcases family_descends (prefixWord ++ tailWord_912951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912957 : List Nat := [1, 4, 1, 3, 3, 2, 1, 3, 4]
def baseStart_912957 : Nat := 118140960795 + 912957 * 2 ^ 59
def prefixEnd_912957 : Nat := 4983230072969 + 3 ^ 40 * 912957 * 2
def baseEnd_912957 : Nat := 104174612863753285608643

theorem tailTrace_912957 : CollatzResearch.WordTrace tailWord_912957 prefixEnd_912957 104174612863753285608643 := by
  unfold tailWord_912957
  simp only [CollatzResearch.WordTrace]
  refine ⟨33298277353520184487233125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22198851569013456324822083 33298277353520184487233125)
  ·
    refine ⟨6243427003785034591356211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33298277353520184487233125 6243427003785034591356211)
    ·
      refine ⟨9365140505677551887034317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6243427003785034591356211 9365140505677551887034317)
      ·
        refine ⟨3511927689629081957637869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9365140505677551887034317 3511927689629081957637869)
        ·
          refine ⟨1316972883610905734114201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3511927689629081957637869 1316972883610905734114201)
          ·
            refine ⟨987729662708179300585651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1316972883610905734114201 987729662708179300585651)
            ·
              refine ⟨1481594494062268950878477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 987729662708179300585651 1481594494062268950878477)
              ·
                refine ⟨555597935273350856579429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1481594494062268950878477 555597935273350856579429)
                ·
                  refine ⟨104174612863753285608643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 555597935273350856579429 104174612863753285608643)
                  ·
                    rfl

theorem cell22_912957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 3, 4].length) (baseStart_912957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_912957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_912957 prefixEnd_912957 := by exact prefixLift 912957
  have htrace : WordTrace (prefixWord ++ tailWord_912957) baseStart_912957 baseEnd_912957 := by
    simpa [prefixWord, tailWord_912957, baseEnd_912957] using wordTrace_append hprefix tailTrace_912957
  have hstable : (prefixWord ++ tailWord_912957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912957).length < 2 ^ (prefixWord ++ tailWord_912957).sum := by decide
  have hdescent : baseEnd_912957 < baseStart_912957 := by decide
  rcases family_descends (prefixWord ++ tailWord_912957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912981 : List Nat := [1, 3, 2, 2, 1, 1, 1, 3, 2, 6]
def baseStart_912981 : Nat := 118140960795 + 912981 * 2 ^ 59
def prefixEnd_912981 : Nat := 4983230072969 + 3 ^ 40 * 912981 * 2
def baseEnd_912981 : Nat := 312532054281731794225855

theorem tailTrace_912981 : CollatzResearch.WordTrace tailWord_912981 prefixEnd_912981 312532054281731794225855 := by
  unfold tailWord_912981
  simp only [CollatzResearch.WordTrace]
  refine ⟨33299152705433236586106797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22199435136955491057404531 33299152705433236586106797)
  ·
    refine ⟨12487182264537463719790049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33299152705433236586106797 12487182264537463719790049)
    ·
      refine ⟨9365386698403097789842537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12487182264537463719790049 9365386698403097789842537)
      ·
        refine ⟨7024040023802323342381903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9365386698403097789842537 7024040023802323342381903)
        ·
          refine ⟨10536060035703485013572855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7024040023802323342381903 10536060035703485013572855)
          ·
            refine ⟨15804090053555227520359283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10536060035703485013572855 15804090053555227520359283)
            ·
              refine ⟨23706135080332841280538925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15804090053555227520359283 23706135080332841280538925)
              ·
                refine ⟨8889800655124815480202097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23706135080332841280538925 8889800655124815480202097)
                ·
                  refine ⟨6667350491343611610151573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8889800655124815480202097 6667350491343611610151573)
                  ·
                    refine ⟨312532054281731794225855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6667350491343611610151573 312532054281731794225855)
                    ·
                      rfl

theorem cell22_912981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_912981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_912981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_912981 prefixEnd_912981 := by exact prefixLift 912981
  have htrace : WordTrace (prefixWord ++ tailWord_912981) baseStart_912981 baseEnd_912981 := by
    simpa [prefixWord, tailWord_912981, baseEnd_912981] using wordTrace_append hprefix tailTrace_912981
  have hstable : (prefixWord ++ tailWord_912981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912981).length < 2 ^ (prefixWord ++ tailWord_912981).sum := by decide
  have hdescent : baseEnd_912981 < baseStart_912981 := by decide
  rcases family_descends (prefixWord ++ tailWord_912981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912989 : List Nat := [1, 4, 4, 2, 1, 1, 1, 3, 2, 3]
def baseStart_912989 : Nat := 118140960795 + 912989 * 2 ^ 59
def prefixEnd_912989 : Nat := 4983230072969 + 3 ^ 40 * 912989 * 2
def baseEnd_912989 : Nat := 312534792845222440025831

theorem tailTrace_912989 : CollatzResearch.WordTrace tailWord_912989 prefixEnd_912989 312534792845222440025831 := by
  unfold tailWord_912989
  simp only [CollatzResearch.WordTrace]
  refine ⟨33299444489404253952398021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22199629659602835968265347 33299444489404253952398021)
  ·
    refine ⟨6243645841763297616074629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33299444489404253952398021 6243645841763297616074629)
    ·
      refine ⟨1170683595330618303013993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6243645841763297616074629 1170683595330618303013993)
      ·
        refine ⟨878012696497963727260495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1170683595330618303013993 878012696497963727260495)
        ·
          refine ⟨1317019044746945590890743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 878012696497963727260495 1317019044746945590890743)
          ·
            refine ⟨1975528567120418386336115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1317019044746945590890743 1975528567120418386336115)
            ·
              refine ⟨2963292850680627579504173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1975528567120418386336115 2963292850680627579504173)
              ·
                refine ⟨1111234819005235342314065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2963292850680627579504173 1111234819005235342314065)
                ·
                  refine ⟨833426114253926506735549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1111234819005235342314065 833426114253926506735549)
                  ·
                    refine ⟨312534792845222440025831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 833426114253926506735549 312534792845222440025831)
                    ·
                      rfl

theorem cell22_912989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_912989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_912989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_912989 prefixEnd_912989 := by exact prefixLift 912989
  have htrace : WordTrace (prefixWord ++ tailWord_912989) baseStart_912989 baseEnd_912989 := by
    simpa [prefixWord, tailWord_912989, baseEnd_912989] using wordTrace_append hprefix tailTrace_912989
  have hstable : (prefixWord ++ tailWord_912989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912989).length < 2 ^ (prefixWord ++ tailWord_912989).sum := by decide
  have hdescent : baseEnd_912989 < baseStart_912989 := by decide
  rcases family_descends (prefixWord ++ tailWord_912989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913034 : List Nat := [3, 1, 2, 3, 2, 1, 4, 2, 1, 3]
def baseStart_913034 : Nat := 118140960795 + 913034 * 2 ^ 59
def prefixEnd_913034 : Nat := 4983230072969 + 3 ^ 40 * 913034 * 2
def baseEnd_913034 : Nat := 312550197264857322650693

theorem tailTrace_913034 : CollatzResearch.WordTrace tailWord_913034 prefixEnd_913034 312550197264857322650693 := by
  unfold tailWord_913034
  simp only [CollatzResearch.WordTrace]
  refine ⟨8325271443560306659446539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22200723849494151091857437 8325271443560306659446539)
  ·
    refine ⟨12487907165340459989169809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8325271443560306659446539 12487907165340459989169809)
    ·
      refine ⟨9365930374005344991877357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12487907165340459989169809 9365930374005344991877357)
      ·
        refine ⟨3512223890252004371954009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9365930374005344991877357 3512223890252004371954009)
        ·
          refine ⟨2634167917689003278965507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3512223890252004371954009 2634167917689003278965507)
          ·
            refine ⟨3951251876533504918448261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2634167917689003278965507 3951251876533504918448261)
            ·
              refine ⟨740859726850032172209049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3951251876533504918448261 740859726850032172209049)
              ·
                refine ⟨555644795137524129156787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 740859726850032172209049 555644795137524129156787)
                ·
                  refine ⟨833467192706286193735181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 555644795137524129156787 833467192706286193735181)
                  ·
                    refine ⟨312550197264857322650693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 833467192706286193735181 312550197264857322650693)
                    ·
                      rfl

theorem cell22_913034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 2, 1, 3].length) (baseStart_913034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_913034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_913034 prefixEnd_913034 := by exact prefixLift 913034
  have htrace : WordTrace (prefixWord ++ tailWord_913034) baseStart_913034 baseEnd_913034 := by
    simpa [prefixWord, tailWord_913034, baseEnd_913034] using wordTrace_append hprefix tailTrace_913034
  have hstable : (prefixWord ++ tailWord_913034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913034).length < 2 ^ (prefixWord ++ tailWord_913034).sum := by decide
  have hdescent : baseEnd_913034 < baseStart_913034 := by decide
  rcases family_descends (prefixWord ++ tailWord_913034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913075 : List Nat := [1, 1, 1, 2, 3, 3, 4, 3, 4]
def baseStart_913075 : Nat := 118140960795 + 913075 * 2 ^ 59
def prefixEnd_913075 : Nat := 4983230072969 + 3 ^ 40 * 913075 * 2
def baseEnd_913075 : Nat := 104188077467582294125189

theorem tailTrace_913075 : CollatzResearch.WordTrace tailWord_913075 prefixEnd_913075 104188077467582294125189 := by
  unfold tailWord_913075
  simp only [CollatzResearch.WordTrace]
  refine ⟨33302581167092690640028679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22201720778061793760019119 33302581167092690640028679)
  ·
    refine ⟨49953871750639035960043019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33302581167092690640028679 49953871750639035960043019)
    ·
      refine ⟨74930807625958553940064529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49953871750639035960043019 74930807625958553940064529)
      ·
        refine ⟨56198105719468915455048397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74930807625958553940064529 56198105719468915455048397)
        ·
          refine ⟨21074289644800843295643149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56198105719468915455048397 21074289644800843295643149)
          ·
            refine ⟨7902858616800316235866181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21074289644800843295643149 7902858616800316235866181)
            ·
              refine ⟨1481785990650059294224909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7902858616800316235866181 1481785990650059294224909)
              ·
                refine ⟨555669746493772235334341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1481785990650059294224909 555669746493772235334341)
                ·
                  refine ⟨104188077467582294125189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 555669746493772235334341 104188077467582294125189)
                  ·
                    rfl

theorem cell22_913075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 3, 4].length) (baseStart_913075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_913075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_913075 prefixEnd_913075 := by exact prefixLift 913075
  have htrace : WordTrace (prefixWord ++ tailWord_913075) baseStart_913075 baseEnd_913075 := by
    simpa [prefixWord, tailWord_913075, baseEnd_913075] using wordTrace_append hprefix tailTrace_913075
  have hstable : (prefixWord ++ tailWord_913075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913075).length < 2 ^ (prefixWord ++ tailWord_913075).sum := by decide
  have hdescent : baseEnd_913075 < baseStart_913075 := by decide
  rcases family_descends (prefixWord ++ tailWord_913075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913077 : List Nat := [1, 3, 3, 3, 2, 1, 1, 3, 1, 4]
def baseStart_913077 : Nat := 118140960795 + 913077 * 2 ^ 59
def prefixEnd_913077 : Nat := 4983230072969 + 3 ^ 40 * 913077 * 2
def baseEnd_913077 : Nat := 312564917043619543825561

theorem tailTrace_913077 : CollatzResearch.WordTrace tailWord_913077 prefixEnd_913077 312564917043619543825561 := by
  unfold tailWord_913077
  simp only [CollatzResearch.WordTrace]
  refine ⟨33302654113085444981601485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22201769408723629987734323 33302654113085444981601485)
  ·
    refine ⟨12488495292407041868100557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33302654113085444981601485 12488495292407041868100557)
    ·
      refine ⟨4683185734652640700537709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12488495292407041868100557 4683185734652640700537709)
      ·
        refine ⟨1756194650494740262701641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4683185734652640700537709 1756194650494740262701641)
        ·
          refine ⟨1317145987871055197026231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1756194650494740262701641 1317145987871055197026231)
          ·
            refine ⟨1975718981806582795539347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1317145987871055197026231 1975718981806582795539347)
            ·
              refine ⟨2963578472709874193309021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1975718981806582795539347 2963578472709874193309021)
              ·
                refine ⟨1111341927266202822490883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2963578472709874193309021 1111341927266202822490883)
                ·
                  refine ⟨1667012890899304233736325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1111341927266202822490883 1667012890899304233736325)
                  ·
                    refine ⟨312564917043619543825561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1667012890899304233736325 312564917043619543825561)
                    ·
                      rfl

theorem cell22_913077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_913077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_913077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_913077 prefixEnd_913077 := by exact prefixLift 913077
  have htrace : WordTrace (prefixWord ++ tailWord_913077) baseStart_913077 baseEnd_913077 := by
    simpa [prefixWord, tailWord_913077, baseEnd_913077] using wordTrace_append hprefix tailTrace_913077
  have hstable : (prefixWord ++ tailWord_913077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913077).length < 2 ^ (prefixWord ++ tailWord_913077).sum := by decide
  have hdescent : baseEnd_913077 < baseStart_913077 := by decide
  rcases family_descends (prefixWord ++ tailWord_913077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913088 : List Nat := [2, 1, 1, 2, 4, 1, 2, 1, 4, 4]
def baseStart_913088 : Nat := 118140960795 + 913088 * 2 ^ 59
def prefixEnd_913088 : Nat := 4983230072969 + 3 ^ 40 * 913088 * 2
def baseEnd_913088 : Nat := 312568682568419181800527

theorem tailTrace_913088 : CollatzResearch.WordTrace tailWord_913088 prefixEnd_913088 312568682568419181800527 := by
  unfold tailWord_913088
  simp only [CollatzResearch.WordTrace]
  refine ⟨16651527658022796930125959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22202036877363729240167945 16651527658022796930125959)
  ·
    refine ⟨24977291487034195395188939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16651527658022796930125959 24977291487034195395188939)
    ·
      refine ⟨37465937230551293092783409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24977291487034195395188939 37465937230551293092783409)
      ·
        refine ⟨28099452922913469819587557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37465937230551293092783409 28099452922913469819587557)
        ·
          refine ⟨5268647423046275591172667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28099452922913469819587557 5268647423046275591172667)
          ·
            refine ⟨7902971134569413386759001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5268647423046275591172667 7902971134569413386759001)
            ·
              refine ⟨5927228350927060040069251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7902971134569413386759001 5927228350927060040069251)
              ·
                refine ⟨8890842526390590060103877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5927228350927060040069251 8890842526390590060103877)
                ·
                  refine ⟨1667032973698235636269477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8890842526390590060103877 1667032973698235636269477)
                  ·
                    refine ⟨312568682568419181800527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1667032973698235636269477 312568682568419181800527)
                    ·
                      rfl

theorem cell22_913088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 4, 4].length) (baseStart_913088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_913088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_913088 prefixEnd_913088 := by exact prefixLift 913088
  have htrace : WordTrace (prefixWord ++ tailWord_913088) baseStart_913088 baseEnd_913088 := by
    simpa [prefixWord, tailWord_913088, baseEnd_913088] using wordTrace_append hprefix tailTrace_913088
  have hstable : (prefixWord ++ tailWord_913088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913088).length < 2 ^ (prefixWord ++ tailWord_913088).sum := by decide
  have hdescent : baseEnd_913088 < baseStart_913088 := by decide
  rcases family_descends (prefixWord ++ tailWord_913088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913148 : List Nat := [2, 2, 2, 1, 3, 1, 1, 3, 7]
def baseStart_913148 : Nat := 118140960795 + 913148 * 2 ^ 59
def prefixEnd_913148 : Nat := 4983230072969 + 3 ^ 40 * 913148 * 2
def baseEnd_913148 : Nat := 104196407264866341766781

theorem tailTrace_913148 : CollatzResearch.WordTrace tailWord_913148 prefixEnd_913148 104196407264866341766781 := by
  unfold tailWord_913148
  simp only [CollatzResearch.WordTrace]
  refine ⟨16652621847914112053718049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22203495797218816071624065 16652621847914112053718049)
  ·
    refine ⟨12489466385935584040288537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16652621847914112053718049 12489466385935584040288537)
    ·
      refine ⟨9367099789451688030216403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12489466385935584040288537 9367099789451688030216403)
      ·
        refine ⟨14050649684177532045324605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9367099789451688030216403 14050649684177532045324605)
        ·
          refine ⟨5268993631566574516996727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14050649684177532045324605 5268993631566574516996727)
          ·
            refine ⟨7903490447349861775495091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5268993631566574516996727 7903490447349861775495091)
            ·
              refine ⟨11855235671024792663242637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7903490447349861775495091 11855235671024792663242637)
              ·
                refine ⟨4445713376634297248715989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11855235671024792663242637 4445713376634297248715989)
                ·
                  refine ⟨104196407264866341766781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4445713376634297248715989 104196407264866341766781)
                  ·
                    rfl

theorem cell22_913148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 7].length) (baseStart_913148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_913148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_913148 prefixEnd_913148 := by exact prefixLift 913148
  have htrace : WordTrace (prefixWord ++ tailWord_913148) baseStart_913148 baseEnd_913148 := by
    simpa [prefixWord, tailWord_913148, baseEnd_913148] using wordTrace_append hprefix tailTrace_913148
  have hstable : (prefixWord ++ tailWord_913148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913148).length < 2 ^ (prefixWord ++ tailWord_913148).sum := by decide
  have hdescent : baseEnd_913148 < baseStart_913148 := by decide
  rcases family_descends (prefixWord ++ tailWord_913148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913163 : List Nat := [1, 1, 1, 1, 5, 1, 2, 3, 2, 5]
def baseStart_913163 : Nat := 118140960795 + 913163 * 2 ^ 59
def prefixEnd_913163 : Nat := 4983230072969 + 3 ^ 40 * 913163 * 2
def baseEnd_913163 : Nat := 312594356601143986175297

theorem tailTrace_913163 : CollatzResearch.WordTrace tailWord_913163 prefixEnd_913163 312594356601143986175297 := by
  unfold tailWord_913163
  simp only [CollatzResearch.WordTrace]
  refine ⟨33305790790773881669232143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22203860527182587779488095 33305790790773881669232143)
  ·
    refine ⟨49958686186160822503848215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33305790790773881669232143 49958686186160822503848215)
    ·
      refine ⟨74938029279241233755772323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49958686186160822503848215 74938029279241233755772323)
      ·
        refine ⟨112407043918861850633658485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74938029279241233755772323 112407043918861850633658485)
        ·
          refine ⟨10538160367393298496905483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112407043918861850633658485 10538160367393298496905483)
          ·
            refine ⟨15807240551089947745358225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10538160367393298496905483 15807240551089947745358225)
            ·
              refine ⟨11855430413317460809018669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15807240551089947745358225 11855430413317460809018669)
              ·
                refine ⟨4445786404994047803382001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11855430413317460809018669 4445786404994047803382001)
                ·
                  refine ⟨3334339803745535852536501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4445786404994047803382001 3334339803745535852536501)
                  ·
                    refine ⟨312594356601143986175297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3334339803745535852536501 312594356601143986175297)
                    ·
                      rfl

theorem cell22_913163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2, 5].length) (baseStart_913163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_913163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_913163 prefixEnd_913163 := by exact prefixLift 913163
  have htrace : WordTrace (prefixWord ++ tailWord_913163) baseStart_913163 baseEnd_913163 := by
    simpa [prefixWord, tailWord_913163, baseEnd_913163] using wordTrace_append hprefix tailTrace_913163
  have hstable : (prefixWord ++ tailWord_913163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913163).length < 2 ^ (prefixWord ++ tailWord_913163).sum := by decide
  have hdescent : baseEnd_913163 < baseStart_913163 := by decide
  rcases family_descends (prefixWord ++ tailWord_913163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913203 : List Nat := [1, 1, 1, 2, 8, 1, 2, 2, 1, 3]
def baseStart_913203 : Nat := 118140960795 + 913203 * 2 ^ 59
def prefixEnd_913203 : Nat := 4983230072969 + 3 ^ 40 * 913203 * 2
def baseEnd_913203 : Nat := 312608049418597215175175

theorem tailTrace_913203 : CollatzResearch.WordTrace tailWord_913203 prefixEnd_913203 312608049418597215175175 := by
  unfold tailWord_913203
  simp only [CollatzResearch.WordTrace]
  refine ⟨33307249710628968500688263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22204833140419312333792175 33307249710628968500688263)
  ·
    refine ⟨49960874565943452751032395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33307249710628968500688263 49960874565943452751032395)
    ·
      refine ⟨74941311848915179126548593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49960874565943452751032395 74941311848915179126548593)
      ·
        refine ⟨56205983886686384344911445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74941311848915179126548593 56205983886686384344911445)
        ·
          refine ⟨658663873672106066541931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 56205983886686384344911445 658663873672106066541931)
          ·
            refine ⟨987995810508159099812897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 658663873672106066541931 987995810508159099812897)
            ·
              refine ⟨740996857881119324859673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 987995810508159099812897 740996857881119324859673)
              ·
                refine ⟨555747643410839493644755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 740996857881119324859673 555747643410839493644755)
                ·
                  refine ⟨833621465116259240467133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 555747643410839493644755 833621465116259240467133)
                  ·
                    refine ⟨312608049418597215175175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 833621465116259240467133 312608049418597215175175)
                    ·
                      rfl

theorem cell22_913203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 2, 1, 3].length) (baseStart_913203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_913203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_913203 prefixEnd_913203 := by exact prefixLift 913203
  have htrace : WordTrace (prefixWord ++ tailWord_913203) baseStart_913203 baseEnd_913203 := by
    simpa [prefixWord, tailWord_913203, baseEnd_913203] using wordTrace_append hprefix tailTrace_913203
  have hstable : (prefixWord ++ tailWord_913203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913203).length < 2 ^ (prefixWord ++ tailWord_913203).sum := by decide
  have hdescent : baseEnd_913203 < baseStart_913203 := by decide
  rcases family_descends (prefixWord ++ tailWord_913203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913225 : List Nat := [1, 2, 1, 1, 2, 4, 4, 1, 1, 5]
def baseStart_913225 : Nat := 118140960795 + 913225 * 2 ^ 59
def prefixEnd_913225 : Nat := 4983230072969 + 3 ^ 40 * 913225 * 2
def baseEnd_913225 : Nat := 312615580468196491125107

theorem tailTrace_913225 : CollatzResearch.WordTrace tailWord_913225 prefixEnd_913225 312615580468196491125107 := by
  unfold tailWord_913225
  simp only [CollatzResearch.WordTrace]
  refine ⟨33308052116549266257989129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22205368077699510838659419 33308052116549266257989129)
  ·
    refine ⟨24981039087411949693491847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33308052116549266257989129 24981039087411949693491847)
    ·
      refine ⟨37471558631117924540237771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24981039087411949693491847 37471558631117924540237771)
      ·
        refine ⟨56207337946676886810356657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37471558631117924540237771 56207337946676886810356657)
        ·
          refine ⟨42155503460007665107767493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56207337946676886810356657 42155503460007665107767493)
          ·
            refine ⟨7904156898751437207706405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42155503460007665107767493 7904156898751437207706405)
            ·
              refine ⟨1482029418515894476444951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7904156898751437207706405 1482029418515894476444951)
              ·
                refine ⟨2223044127773841714667427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1482029418515894476444951 2223044127773841714667427)
                ·
                  refine ⟨3334566191660762572001141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2223044127773841714667427 3334566191660762572001141)
                  ·
                    refine ⟨312615580468196491125107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3334566191660762572001141 312615580468196491125107)
                    ·
                      rfl

theorem cell22_913225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 1, 1, 5].length) (baseStart_913225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_913225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_913225 prefixEnd_913225 := by exact prefixLift 913225
  have htrace : WordTrace (prefixWord ++ tailWord_913225) baseStart_913225 baseEnd_913225 := by
    simpa [prefixWord, tailWord_913225, baseEnd_913225] using wordTrace_append hprefix tailTrace_913225
  have hstable : (prefixWord ++ tailWord_913225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913225).length < 2 ^ (prefixWord ++ tailWord_913225).sum := by decide
  have hdescent : baseEnd_913225 < baseStart_913225 := by decide
  rcases family_descends (prefixWord ++ tailWord_913225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913360 : List Nat := [2, 1, 1, 1, 1, 2, 5, 1, 3, 5]
def baseStart_913360 : Nat := 118140960795 + 913360 * 2 ^ 59
def prefixEnd_913360 : Nat := 4983230072969 + 3 ^ 40 * 913360 * 2
def baseEnd_913360 : Nat := 312661793727101138999693

theorem tailTrace_913360 : CollatzResearch.WordTrace tailWord_913360 prefixEnd_913360 312661793727101138999693 := by
  unfold tailWord_913360
  simp only [CollatzResearch.WordTrace]
  refine ⟨16656487985530092157076767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22208650647373456209435689 16656487985530092157076767)
  ·
    refine ⟨24984731978295138235615151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16656487985530092157076767 24984731978295138235615151)
    ·
      refine ⟨37477097967442707353422727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24984731978295138235615151 37477097967442707353422727)
      ·
        refine ⟨56215646951164061030134091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37477097967442707353422727 56215646951164061030134091)
        ·
          refine ⟨84323470426746091545201137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56215646951164061030134091 84323470426746091545201137)
          ·
            refine ⟨63242602820059568658900853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84323470426746091545201137 63242602820059568658900853)
            ·
              refine ⟨5928994014380584561771955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63242602820059568658900853 5928994014380584561771955)
              ·
                refine ⟨8893491021570876842657933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5928994014380584561771955 8893491021570876842657933)
                ·
                  refine ⟨3335059133089078815996725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8893491021570876842657933 3335059133089078815996725)
                  ·
                    refine ⟨312661793727101138999693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3335059133089078815996725 312661793727101138999693)
                    ·
                      rfl

theorem cell22_913360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 3, 5].length) (baseStart_913360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_913360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_913360 prefixEnd_913360 := by exact prefixLift 913360
  have htrace : WordTrace (prefixWord ++ tailWord_913360) baseStart_913360 baseEnd_913360 := by
    simpa [prefixWord, tailWord_913360, baseEnd_913360] using wordTrace_append hprefix tailTrace_913360
  have hstable : (prefixWord ++ tailWord_913360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913360).length < 2 ^ (prefixWord ++ tailWord_913360).sum := by decide
  have hdescent : baseEnd_913360 < baseStart_913360 := by decide
  rcases family_descends (prefixWord ++ tailWord_913360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913377 : List Nat := [1, 2, 3, 1, 2, 1, 2, 3, 4, 3]
def baseStart_913377 : Nat := 118140960795 + 913377 * 2 ^ 59
def prefixEnd_913377 : Nat := 4983230072969 + 3 ^ 40 * 913377 * 2
def baseEnd_913377 : Nat := 312667613174518761324641

theorem tailTrace_913377 : CollatzResearch.WordTrace tailWord_913377 prefixEnd_913377 312667613174518761324641 := by
  unfold tailWord_913377
  simp only [CollatzResearch.WordTrace]
  refine ⟨33313596011998596217522385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22209064007999064145014923 33313596011998596217522385)
  ·
    refine ⟨24985197008998947163141789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33313596011998596217522385 24985197008998947163141789)
    ·
      refine ⟨9369448878374605186178171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24985197008998947163141789 9369448878374605186178171)
      ·
        refine ⟨14054173317561907779267257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9369448878374605186178171 14054173317561907779267257)
        ·
          refine ⟨10540629988171430834450443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14054173317561907779267257 10540629988171430834450443)
          ·
            refine ⟨15810944982257146251675665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10540629988171430834450443 15810944982257146251675665)
            ·
              refine ⟨11858208736692859688756749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15810944982257146251675665 11858208736692859688756749)
              ·
                refine ⟨4446828276259822383283781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11858208736692859688756749 4446828276259822383283781)
                ·
                  refine ⟨833780301798716696865709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4446828276259822383283781 833780301798716696865709)
                  ·
                    refine ⟨312667613174518761324641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 833780301798716696865709 312667613174518761324641)
                    ·
                      rfl

theorem cell22_913377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 4, 3].length) (baseStart_913377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_913377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_913377 prefixEnd_913377 := by exact prefixLift 913377
  have htrace : WordTrace (prefixWord ++ tailWord_913377) baseStart_913377 baseEnd_913377 := by
    simpa [prefixWord, tailWord_913377, baseEnd_913377] using wordTrace_append hprefix tailTrace_913377
  have hstable : (prefixWord ++ tailWord_913377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913377).length < 2 ^ (prefixWord ++ tailWord_913377).sum := by decide
  have hdescent : baseEnd_913377 < baseStart_913377 := by decide
  rcases family_descends (prefixWord ++ tailWord_913377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913379 : List Nat := [1, 1, 1, 6, 1, 3, 1, 4, 4]
def baseStart_913379 : Nat := 118140960795 + 913379 * 2 ^ 59
def prefixEnd_913379 : Nat := 4983230072969 + 3 ^ 40 * 913379 * 2
def baseEnd_913379 : Nat := 104222765938463807591545

theorem tailTrace_913379 : CollatzResearch.WordTrace tailWord_913379 prefixEnd_913379 104222765938463807591545 := by
  unfold tailWord_913379
  simp only [CollatzResearch.WordTrace]
  refine ⟨33313668957991350559095191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22209112638660900372730127 33313668957991350559095191)
  ·
    refine ⟨49970503436987025838642787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33313668957991350559095191 49970503436987025838642787)
    ·
      refine ⟨74955755155480538757964181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49970503436987025838642787 74955755155480538757964181)
      ·
        refine ⟨3513551022913150254279571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 74955755155480538757964181 3513551022913150254279571)
        ·
          refine ⟨5270326534369725381419357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3513551022913150254279571 5270326534369725381419357)
          ·
            refine ⟨1976372450388647018032259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5270326534369725381419357 1976372450388647018032259)
            ·
              refine ⟨2964558675582970527048389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1976372450388647018032259 2964558675582970527048389)
              ·
                refine ⟨555854751671806973821573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2964558675582970527048389 555854751671806973821573)
                ·
                  refine ⟨104222765938463807591545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 555854751671806973821573 104222765938463807591545)
                  ·
                    rfl

theorem cell22_913379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 4, 4].length) (baseStart_913379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_913379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_913379 prefixEnd_913379 := by exact prefixLift 913379
  have htrace : WordTrace (prefixWord ++ tailWord_913379) baseStart_913379 baseEnd_913379 := by
    simpa [prefixWord, tailWord_913379, baseEnd_913379] using wordTrace_append hprefix tailTrace_913379
  have hstable : (prefixWord ++ tailWord_913379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913379).length < 2 ^ (prefixWord ++ tailWord_913379).sum := by decide
  have hdescent : baseEnd_913379 < baseStart_913379 := by decide
  rcases family_descends (prefixWord ++ tailWord_913379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913428 : List Nat := [2, 4, 3, 2, 1, 1, 1, 1, 4, 3]
def baseStart_913428 : Nat := 118140960795 + 913428 * 2 ^ 59
def prefixEnd_913428 : Nat := 4983230072969 + 3 ^ 40 * 913428 * 2
def baseEnd_913428 : Nat := 312685071516771628299485

theorem tailTrace_913428 : CollatzResearch.WordTrace tailWord_913428 prefixEnd_913428 312685071516771628299485 := by
  unfold tailWord_913428
  simp only [CollatzResearch.WordTrace]
  refine ⟨16657728067406915963814469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22210304089875887951752625 16657728067406915963814469)
  ·
    refine ⟨3123324012638796743215213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16657728067406915963814469 3123324012638796743215213)
    ·
      refine ⟨1171246504739548778705705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3123324012638796743215213 1171246504739548778705705)
      ·
        refine ⟨878434878554661584029279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1171246504739548778705705 878434878554661584029279)
        ·
          refine ⟨1317652317831992376043919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 878434878554661584029279 1317652317831992376043919)
          ·
            refine ⟨1976478476747988564065879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1317652317831992376043919 1976478476747988564065879)
            ·
              refine ⟨2964717715121982846098819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1976478476747988564065879 2964717715121982846098819)
              ·
                refine ⟨4447076572682974269148229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2964717715121982846098819 4447076572682974269148229)
                ·
                  refine ⟨833826857378057675465293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4447076572682974269148229 833826857378057675465293)
                  ·
                    refine ⟨312685071516771628299485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 833826857378057675465293 312685071516771628299485)
                    ·
                      rfl

theorem cell22_913428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_913428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_913428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_913428 prefixEnd_913428 := by exact prefixLift 913428
  have htrace : WordTrace (prefixWord ++ tailWord_913428) baseStart_913428 baseEnd_913428 := by
    simpa [prefixWord, tailWord_913428, baseEnd_913428] using wordTrace_append hprefix tailTrace_913428
  have hstable : (prefixWord ++ tailWord_913428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913428).length < 2 ^ (prefixWord ++ tailWord_913428).sum := by decide
  have hdescent : baseEnd_913428 < baseStart_913428 := by decide
  rcases family_descends (prefixWord ++ tailWord_913428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913439 : List Nat := [1, 1, 2, 4, 1, 2, 4, 1, 3, 3]
def baseStart_913439 : Nat := 118140960795 + 913439 * 2 ^ 59
def prefixEnd_913439 : Nat := 4983230072969 + 3 ^ 40 * 913439 * 2
def baseEnd_913439 : Nat := 312688837041571266274451

theorem tailTrace_913439 : CollatzResearch.WordTrace tailWord_913439 prefixEnd_913439 312688837041571266274451 := by
  unfold tailWord_913439
  simp only [CollatzResearch.WordTrace]
  refine ⟨33315857337773980806279371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22210571558515987204186247 33315857337773980806279371)
  ·
    refine ⟨49973786006660971209419057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33315857337773980806279371 49973786006660971209419057)
    ·
      refine ⟨37480339504995728407064293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49973786006660971209419057 37480339504995728407064293)
      ·
        refine ⟨7027563657186699076324555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37480339504995728407064293 7027563657186699076324555)
        ·
          refine ⟨10541345485780048614486833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7027563657186699076324555 10541345485780048614486833)
          ·
            refine ⟨7906009114335036460865125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10541345485780048614486833 7906009114335036460865125)
            ·
              refine ⟨1482376708937819336412211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7906009114335036460865125 1482376708937819336412211)
              ·
                refine ⟨2223565063406729004618317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1482376708937819336412211 2223565063406729004618317)
                ·
                  refine ⟨833836898777523376731869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2223565063406729004618317 833836898777523376731869)
                  ·
                    refine ⟨312688837041571266274451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 833836898777523376731869 312688837041571266274451)
                    ·
                      rfl

theorem cell22_913439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 1, 3, 3].length) (baseStart_913439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_913439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_913439 prefixEnd_913439 := by exact prefixLift 913439
  have htrace : WordTrace (prefixWord ++ tailWord_913439) baseStart_913439 baseEnd_913439 := by
    simpa [prefixWord, tailWord_913439, baseEnd_913439] using wordTrace_append hprefix tailTrace_913439
  have hstable : (prefixWord ++ tailWord_913439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913439).length < 2 ^ (prefixWord ++ tailWord_913439).sum := by decide
  have hdescent : baseEnd_913439 < baseStart_913439 := by decide
  rcases family_descends (prefixWord ++ tailWord_913439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913473 : List Nat := [1, 2, 5, 1, 2, 1, 3, 3, 1, 3]
def baseStart_913473 : Nat := 118140960795 + 913473 * 2 ^ 59
def prefixEnd_913473 : Nat := 4983230072969 + 3 ^ 40 * 913473 * 2
def baseEnd_913473 : Nat := 312700475936406510924347

theorem tailTrace_913473 : CollatzResearch.WordTrace tailWord_913473 prefixEnd_913473 312700475936406510924347 := by
  unfold tailWord_913473
  simp only [CollatzResearch.WordTrace]
  refine ⟨33317097419650804613017073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22211398279767203075344715 33317097419650804613017073)
  ·
    refine ⟨24987823064738103459762805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33317097419650804613017073 24987823064738103459762805)
    ·
      refine ⟨2342608412319197199352763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24987823064738103459762805 2342608412319197199352763)
      ·
        refine ⟨3513912618478795799029145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2342608412319197199352763 3513912618478795799029145)
        ·
          refine ⟨2635434463859096849271859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3513912618478795799029145 2635434463859096849271859)
          ·
            refine ⟨3953151695788645273907789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2635434463859096849271859 3953151695788645273907789)
            ·
              refine ⟨1482431885920741977715421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3953151695788645273907789 1482431885920741977715421)
              ·
                refine ⟨555911957220278241643283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1482431885920741977715421 555911957220278241643283)
                ·
                  refine ⟨833867935830417362464925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 555911957220278241643283 833867935830417362464925)
                  ·
                    refine ⟨312700475936406510924347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 833867935830417362464925 312700475936406510924347)
                    ·
                      rfl

theorem cell22_913473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_913473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_913473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_913473 prefixEnd_913473 := by exact prefixLift 913473
  have htrace : WordTrace (prefixWord ++ tailWord_913473) baseStart_913473 baseEnd_913473 := by
    simpa [prefixWord, tailWord_913473, baseEnd_913473] using wordTrace_append hprefix tailTrace_913473
  have hstable : (prefixWord ++ tailWord_913473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913473).length < 2 ^ (prefixWord ++ tailWord_913473).sum := by decide
  have hdescent : baseEnd_913473 < baseStart_913473 := by decide
  rcases family_descends (prefixWord ++ tailWord_913473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913482 : List Nat := [3, 1, 2, 1, 1, 2, 1, 2, 5, 4]
def baseStart_913482 : Nat := 118140960795 + 913482 * 2 ^ 59
def prefixEnd_913482 : Nat := 4983230072969 + 3 ^ 40 * 913482 * 2
def baseEnd_913482 : Nat := 312703556820333487449319

theorem tailTrace_913482 : CollatzResearch.WordTrace tailWord_913482 prefixEnd_913482 312703556820333487449319 := by
  unfold tailWord_913482
  simp only [CollatzResearch.WordTrace]
  refine ⟨8329356419154549787523675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22211617117745466100063133 8329356419154549787523675)
  ·
    refine ⟨12494034628731824681285513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8329356419154549787523675 12494034628731824681285513)
    ·
      refine ⟨9370525971548868510964135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12494034628731824681285513 9370525971548868510964135)
      ·
        refine ⟨14055788957323302766446203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9370525971548868510964135 14055788957323302766446203)
        ·
          refine ⟨21083683435984954149669305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14055788957323302766446203 21083683435984954149669305)
          ·
            refine ⟨15812762576988715612251979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21083683435984954149669305 15812762576988715612251979)
            ·
              refine ⟨23719143865483073418377969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15812762576988715612251979 23719143865483073418377969)
              ·
                refine ⟨17789357899112305063783477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23719143865483073418377969 17789357899112305063783477)
                ·
                  refine ⟨1667752303041778599729701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17789357899112305063783477 1667752303041778599729701)
                  ·
                    refine ⟨312703556820333487449319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1667752303041778599729701 312703556820333487449319)
                    ·
                      rfl

theorem cell22_913482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_913482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_913482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_913482 prefixEnd_913482 := by exact prefixLift 913482
  have htrace : WordTrace (prefixWord ++ tailWord_913482) baseStart_913482 baseEnd_913482 := by
    simpa [prefixWord, tailWord_913482, baseEnd_913482] using wordTrace_append hprefix tailTrace_913482
  have hstable : (prefixWord ++ tailWord_913482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913482).length < 2 ^ (prefixWord ++ tailWord_913482).sum := by decide
  have hdescent : baseEnd_913482 < baseStart_913482 := by decide
  rcases family_descends (prefixWord ++ tailWord_913482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913490 : List Nat := [3, 2, 2, 1, 4, 1, 3, 2, 1, 3]
def baseStart_913490 : Nat := 118140960795 + 913490 * 2 ^ 59
def prefixEnd_913490 : Nat := 4983230072969 + 3 ^ 40 * 913490 * 2
def baseEnd_913490 : Nat := 312706295383824133249295

theorem tailTrace_913490 : CollatzResearch.WordTrace tailWord_913490 prefixEnd_913490 312706295383824133249295 := by
  unfold tailWord_913490
  simp only [CollatzResearch.WordTrace]
  refine ⟨8329429365147304129096481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22211811640392811010923949 8329429365147304129096481)
  ·
    refine ⟨6247072023860478096822361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8329429365147304129096481 6247072023860478096822361)
    ·
      refine ⟨4685304017895358572616771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6247072023860478096822361 4685304017895358572616771)
      ·
        refine ⟨7027956026843037858925157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4685304017895358572616771 7027956026843037858925157)
        ·
          refine ⟨1317741755033069598548467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7027956026843037858925157 1317741755033069598548467)
          ·
            refine ⟨1976612632549604397822701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1317741755033069598548467 1976612632549604397822701)
            ·
              refine ⟨741229737206101649183513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1976612632549604397822701 741229737206101649183513)
              ·
                refine ⟨555922302904576236887635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 741229737206101649183513 555922302904576236887635)
                ·
                  refine ⟨833883454356864355331453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 555922302904576236887635 833883454356864355331453)
                  ·
                    refine ⟨312706295383824133249295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 833883454356864355331453 312706295383824133249295)
                    ·
                      rfl

theorem cell22_913490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 2, 1, 3].length) (baseStart_913490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_913490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_913490 prefixEnd_913490 := by exact prefixLift 913490
  have htrace : WordTrace (prefixWord ++ tailWord_913490) baseStart_913490 baseEnd_913490 := by
    simpa [prefixWord, tailWord_913490, baseEnd_913490] using wordTrace_append hprefix tailTrace_913490
  have hstable : (prefixWord ++ tailWord_913490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913490).length < 2 ^ (prefixWord ++ tailWord_913490).sum := by decide
  have hdescent : baseEnd_913490 < baseStart_913490 := by decide
  rcases family_descends (prefixWord ++ tailWord_913490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913516 : List Nat := [2, 2, 1, 1, 3, 5, 1, 2, 1, 4]
def baseStart_913516 : Nat := 118140960795 + 913516 * 2 ^ 59
def prefixEnd_913516 : Nat := 4983230072969 + 3 ^ 40 * 913516 * 2
def baseEnd_913516 : Nat := 312715195715168732099215

theorem tailTrace_913516 : CollatzResearch.WordTrace tailWord_913516 prefixEnd_913516 312715195715168732099215 := by
  unfold tailWord_913516
  simp only [CollatzResearch.WordTrace]
  refine ⟨16659332879247511478416201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22212443838996681971221601 16659332879247511478416201)
  ·
    refine ⟨12494499659435633608812151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16659332879247511478416201 12494499659435633608812151)
    ·
      refine ⟨18741749489153450413218227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12494499659435633608812151 18741749489153450413218227)
      ·
        refine ⟨28112624233730175619827341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18741749489153450413218227 28112624233730175619827341)
        ·
          refine ⟨10542234087648815857435253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28112624233730175619827341 10542234087648815857435253)
          ·
            refine ⟨988334445717076486634555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10542234087648815857435253 988334445717076486634555)
            ·
              refine ⟨1482501668575614729951833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 988334445717076486634555 1482501668575614729951833)
              ·
                refine ⟨1111876251431711047463875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1482501668575614729951833 1111876251431711047463875)
                ·
                  refine ⟨1667814377147566571195813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1111876251431711047463875 1667814377147566571195813)
                  ·
                    refine ⟨312715195715168732099215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1667814377147566571195813 312715195715168732099215)
                    ·
                      rfl

theorem cell22_913516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 4].length) (baseStart_913516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_913516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_913516 prefixEnd_913516 := by exact prefixLift 913516
  have htrace : WordTrace (prefixWord ++ tailWord_913516) baseStart_913516 baseEnd_913516 := by
    simpa [prefixWord, tailWord_913516, baseEnd_913516] using wordTrace_append hprefix tailTrace_913516
  have hstable : (prefixWord ++ tailWord_913516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913516).length < 2 ^ (prefixWord ++ tailWord_913516).sum := by decide
  have hdescent : baseEnd_913516 < baseStart_913516 := by decide
  rcases family_descends (prefixWord ++ tailWord_913516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913529 : List Nat := [1, 2, 1, 3, 4, 2, 1, 2, 1, 5]
def baseStart_913529 : Nat := 118140960795 + 913529 * 2 ^ 59
def prefixEnd_913529 : Nat := 4983230072969 + 3 ^ 40 * 913529 * 2
def baseEnd_913529 : Nat := 312719645880841031524175

theorem tailTrace_913529 : CollatzResearch.WordTrace tailWord_913529 prefixEnd_913529 312719645880841031524175 := by
  unfold tailWord_913529
  simp only [CollatzResearch.WordTrace]
  refine ⟨33319139907447926177055641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22212759938298617451370427 33319139907447926177055641)
  ·
    refine ⟨24989354930585944632791731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33319139907447926177055641 24989354930585944632791731)
    ·
      refine ⟨37484032395878916949187597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24989354930585944632791731 37484032395878916949187597)
      ·
        refine ⟨14056512148454593855945349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37484032395878916949187597 14056512148454593855945349)
        ·
          refine ⟨2635596027835236347989753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14056512148454593855945349 2635596027835236347989753)
          ·
            refine ⟨1976697020876427260992315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2635596027835236347989753 1976697020876427260992315)
            ·
              refine ⟨2965045531314640891488473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1976697020876427260992315 2965045531314640891488473)
              ·
                refine ⟨2223784148485980668616355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2965045531314640891488473 2223784148485980668616355)
                ·
                  refine ⟨3335676222728971002924533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2223784148485980668616355 3335676222728971002924533)
                  ·
                    refine ⟨312719645880841031524175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3335676222728971002924533 312719645880841031524175)
                    ·
                      rfl

theorem cell22_913529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 2, 1, 5].length) (baseStart_913529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_913529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_913529 prefixEnd_913529 := by exact prefixLift 913529
  have htrace : WordTrace (prefixWord ++ tailWord_913529) baseStart_913529 baseEnd_913529 := by
    simpa [prefixWord, tailWord_913529, baseEnd_913529] using wordTrace_append hprefix tailTrace_913529
  have hstable : (prefixWord ++ tailWord_913529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913529).length < 2 ^ (prefixWord ++ tailWord_913529).sum := by decide
  have hdescent : baseEnd_913529 < baseStart_913529 := by decide
  rcases family_descends (prefixWord ++ tailWord_913529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913546 : List Nat := [3, 1, 2, 3, 1, 2, 1, 4, 2, 3]
def baseStart_913546 : Nat := 118140960795 + 913546 * 2 ^ 59
def prefixEnd_913546 : Nat := 4983230072969 + 3 ^ 40 * 913546 * 2
def baseEnd_913546 : Nat := 312725465328258653849123

theorem tailTrace_913546 : CollatzResearch.WordTrace tailWord_913546 prefixEnd_913546 312725465328258653849123 := by
  unfold tailWord_913546
  simp only [CollatzResearch.WordTrace]
  refine ⟨8329939987096584520106123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22213173298924225386949661 8329939987096584520106123)
  ·
    refine ⟨12494909980644876780159185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8329939987096584520106123 12494909980644876780159185)
    ·
      refine ⟨9371182485483657585119389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12494909980644876780159185 9371182485483657585119389)
      ·
        refine ⟨3514193432056371594419771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9371182485483657585119389 3514193432056371594419771)
        ·
          refine ⟨5271290148084557391629657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3514193432056371594419771 5271290148084557391629657)
          ·
            refine ⟨3953467611063418043722243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5271290148084557391629657 3953467611063418043722243)
            ·
              refine ⟨5930201416595127065583365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3953467611063418043722243 5930201416595127065583365)
              ·
                refine ⟨1111912765611586324796881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5930201416595127065583365 1111912765611586324796881)
                ·
                  refine ⟨833934574208689743597661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1111912765611586324796881 833934574208689743597661)
                  ·
                    refine ⟨312725465328258653849123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 833934574208689743597661 312725465328258653849123)
                    ·
                      rfl

theorem cell22_913546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 4, 2, 3].length) (baseStart_913546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_913546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_913546 prefixEnd_913546 := by exact prefixLift 913546
  have htrace : WordTrace (prefixWord ++ tailWord_913546) baseStart_913546 baseEnd_913546 := by
    simpa [prefixWord, tailWord_913546, baseEnd_913546] using wordTrace_append hprefix tailTrace_913546
  have hstable : (prefixWord ++ tailWord_913546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913546).length < 2 ^ (prefixWord ++ tailWord_913546).sum := by decide
  have hdescent : baseEnd_913546 < baseStart_913546 := by decide
  rcases family_descends (prefixWord ++ tailWord_913546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913587 : List Nat := [1, 1, 1, 2, 3, 2, 1, 4, 7]
def baseStart_913587 : Nat := 118140960795 + 913587 * 2 ^ 59
def prefixEnd_913587 : Nat := 4983230072969 + 3 ^ 40 * 913587 * 2
def baseEnd_913587 : Nat := 104246500155382737857999

theorem tailTrace_913587 : CollatzResearch.WordTrace tailWord_913587 prefixEnd_913587 104246500155382737857999 := by
  unfold tailWord_913587
  simp only [CollatzResearch.WordTrace]
  refine ⟨33321255341237802082667015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22214170227491868055111343 33321255341237802082667015)
  ·
    refine ⟨49981883011856703124000523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33321255341237802082667015 49981883011856703124000523)
    ·
      refine ⟨74972824517785054686000785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49981883011856703124000523 74972824517785054686000785)
      ·
        refine ⟨56229618388338791014500589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74972824517785054686000785 56229618388338791014500589)
        ·
          refine ⟨21086106895627046630437721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56229618388338791014500589 21086106895627046630437721)
          ·
            refine ⟨15814580171720284972828291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21086106895627046630437721 15814580171720284972828291)
            ·
              refine ⟨23721870257580427459242437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15814580171720284972828291 23721870257580427459242437)
              ·
                refine ⟨4447850673296330148607957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23721870257580427459242437 4447850673296330148607957)
                ·
                  refine ⟨104246500155382737857999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4447850673296330148607957 104246500155382737857999)
                  ·
                    rfl

theorem cell22_913587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 7].length) (baseStart_913587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_913587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_913587 prefixEnd_913587 := by exact prefixLift 913587
  have htrace : WordTrace (prefixWord ++ tailWord_913587) baseStart_913587 baseEnd_913587 := by
    simpa [prefixWord, tailWord_913587, baseEnd_913587] using wordTrace_append hprefix tailTrace_913587
  have hstable : (prefixWord ++ tailWord_913587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913587).length < 2 ^ (prefixWord ++ tailWord_913587).sum := by decide
  have hdescent : baseEnd_913587 < baseStart_913587 := by decide
  rcases family_descends (prefixWord ++ tailWord_913587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913696 : List Nat := [2, 1, 1, 5, 2, 1, 1, 3, 2, 4]
def baseStart_913696 : Nat := 118140960795 + 913696 * 2 ^ 59
def prefixEnd_913696 : Nat := 4983230072969 + 3 ^ 40 * 913696 * 2
def baseEnd_913696 : Nat := 312776813393708262598663

theorem tailTrace_913696 : CollatzResearch.WordTrace tailWord_913696 prefixEnd_913696 312776813393708262598663 := by
  unfold tailWord_913696
  simp only [CollatzResearch.WordTrace]
  refine ⟨16662615448921456849192471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22216820598561942465589961 16662615448921456849192471)
  ·
    refine ⟨24993923173382185273788707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16662615448921456849192471 24993923173382185273788707)
    ·
      refine ⟨37490884760073277910683061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24993923173382185273788707 37490884760073277910683061)
      ·
        refine ⟨3514770446256869804126537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37490884760073277910683061 3514770446256869804126537)
        ·
          refine ⟨2636077834692652353094903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3514770446256869804126537 2636077834692652353094903)
          ·
            refine ⟨3954116752038978529642355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2636077834692652353094903 3954116752038978529642355)
            ·
              refine ⟨5931175128058467794463533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3954116752038978529642355 5931175128058467794463533)
              ·
                refine ⟨2224190673021925422923825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5931175128058467794463533 2224190673021925422923825)
                ·
                  refine ⟨1668143004766444067192869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2224190673021925422923825 1668143004766444067192869)
                  ·
                    refine ⟨312776813393708262598663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1668143004766444067192869 312776813393708262598663)
                    ·
                      rfl

theorem cell22_913696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3, 2, 4].length) (baseStart_913696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_913696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_913696 prefixEnd_913696 := by exact prefixLift 913696
  have htrace : WordTrace (prefixWord ++ tailWord_913696) baseStart_913696 baseEnd_913696 := by
    simpa [prefixWord, tailWord_913696, baseEnd_913696] using wordTrace_append hprefix tailTrace_913696
  have hstable : (prefixWord ++ tailWord_913696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913696).length < 2 ^ (prefixWord ++ tailWord_913696).sum := by decide
  have hdescent : baseEnd_913696 < baseStart_913696 := by decide
  rcases family_descends (prefixWord ++ tailWord_913696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913724 : List Nat := [2, 2, 2, 2, 1, 2, 1, 1, 1, 8]
def baseStart_913724 : Nat := 118140960795 + 913724 * 2 ^ 59
def prefixEnd_913724 : Nat := 4983230072969 + 3 ^ 40 * 913724 * 2
def baseEnd_913724 : Nat := 312786398365925522898577

theorem tailTrace_913724 : CollatzResearch.WordTrace tailWord_913724 prefixEnd_913724 312786398365925522898577 := by
  unfold tailWord_913724
  simp only [CollatzResearch.WordTrace]
  refine ⟨16663126070870737240202113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22217501427827649653602817 16663126070870737240202113)
  ·
    refine ⟨12497344553153052930151585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16663126070870737240202113 12497344553153052930151585)
    ·
      refine ⟨9373008414864789697613689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12497344553153052930151585 9373008414864789697613689)
      ·
        refine ⟨7029756311148592273210267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9373008414864789697613689 7029756311148592273210267)
        ·
          refine ⟨10544634466722888409815401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7029756311148592273210267 10544634466722888409815401)
          ·
            refine ⟨7908475850042166307361551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10544634466722888409815401 7908475850042166307361551)
            ·
              refine ⟨11862713775063249461042327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7908475850042166307361551 11862713775063249461042327)
              ·
                refine ⟨17794070662594874191563491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11862713775063249461042327 17794070662594874191563491)
                ·
                  refine ⟨26691105993892311287345237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17794070662594874191563491 26691105993892311287345237)
                  ·
                    refine ⟨312786398365925522898577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 26691105993892311287345237 312786398365925522898577)
                    ·
                      rfl

theorem cell22_913724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_913724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_913724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_913724 prefixEnd_913724 := by exact prefixLift 913724
  have htrace : WordTrace (prefixWord ++ tailWord_913724) baseStart_913724 baseEnd_913724 := by
    simpa [prefixWord, tailWord_913724, baseEnd_913724] using wordTrace_append hprefix tailTrace_913724
  have hstable : (prefixWord ++ tailWord_913724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913724).length < 2 ^ (prefixWord ++ tailWord_913724).sum := by decide
  have hdescent : baseEnd_913724 < baseStart_913724 := by decide
  rcases family_descends (prefixWord ++ tailWord_913724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913754 : List Nat := [3, 1, 1, 2, 1, 2, 1, 1, 3, 7]
def baseStart_913754 : Nat := 118140960795 + 913754 * 2 ^ 59
def prefixEnd_913754 : Nat := 4983230072969 + 3 ^ 40 * 913754 * 2
def baseEnd_913754 : Nat := 312796667979015444648485

theorem tailTrace_913754 : CollatzResearch.WordTrace tailWord_913754 prefixEnd_913754 312796667979015444648485 := by
  unfold tailWord_913754
  simp only [CollatzResearch.WordTrace]
  refine ⟨8331836582908197400999079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22218230887755193069330877 8331836582908197400999079)
  ·
    refine ⟨12497754874362296101498619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8331836582908197400999079 12497754874362296101498619)
    ·
      refine ⟨18746632311543444152247929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12497754874362296101498619 18746632311543444152247929)
      ·
        refine ⟨14059974233657583114185947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18746632311543444152247929 14059974233657583114185947)
        ·
          refine ⟨21089961350486374671278921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14059974233657583114185947 21089961350486374671278921)
          ·
            refine ⟨15817471012864781003459191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21089961350486374671278921 15817471012864781003459191)
            ·
              refine ⟨23726206519297171505188787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15817471012864781003459191 23726206519297171505188787)
              ·
                refine ⟨35589309778945757257783181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23726206519297171505188787 35589309778945757257783181)
                ·
                  refine ⟨13345991167104658971668693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35589309778945757257783181 13345991167104658971668693)
                  ·
                    refine ⟨312796667979015444648485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13345991167104658971668693 312796667979015444648485)
                    ·
                      rfl

theorem cell22_913754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 3, 7].length) (baseStart_913754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_913754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_913754 prefixEnd_913754 := by exact prefixLift 913754
  have htrace : WordTrace (prefixWord ++ tailWord_913754) baseStart_913754 baseEnd_913754 := by
    simpa [prefixWord, tailWord_913754, baseEnd_913754] using wordTrace_append hprefix tailTrace_913754
  have hstable : (prefixWord ++ tailWord_913754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913754).length < 2 ^ (prefixWord ++ tailWord_913754).sum := by decide
  have hdescent : baseEnd_913754 < baseStart_913754 := by decide
  rcases family_descends (prefixWord ++ tailWord_913754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913801 : List Nat := [1, 2, 1, 1, 6, 1, 2, 2, 6]
def baseStart_913801 : Nat := 118140960795 + 913801 * 2 ^ 59
def prefixEnd_913801 : Nat := 4983230072969 + 3 ^ 40 * 913801 * 2
def baseEnd_913801 : Nat := 104270919013174329574447

theorem tailTrace_913801 : CollatzResearch.WordTrace tailWord_913801 prefixEnd_913801 104270919013174329574447 := by
  unfold tailWord_913801
  simp only [CollatzResearch.WordTrace]
  refine ⟨33329060562462516630957257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22219373708308344420638171 33329060562462516630957257)
  ·
    refine ⟨24996795421846887473217943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33329060562462516630957257 24996795421846887473217943)
    ·
      refine ⟨37495193132770331209826915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24996795421846887473217943 37495193132770331209826915)
      ·
        refine ⟨56242789699155496814740373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37495193132770331209826915 56242789699155496814740373)
        ·
          refine ⟨2636380767147913913190955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 56242789699155496814740373 2636380767147913913190955)
          ·
            refine ⟨3954571150721870869786433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2636380767147913913190955 3954571150721870869786433)
            ·
              refine ⟨2965928363041403152339825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3954571150721870869786433 2965928363041403152339825)
              ·
                refine ⟨2224446272281052364254869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2965928363041403152339825 2224446272281052364254869)
                ·
                  refine ⟨104270919013174329574447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2224446272281052364254869 104270919013174329574447)
                  ·
                    rfl

theorem cell22_913801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2, 6].length) (baseStart_913801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_913801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_913801 prefixEnd_913801 := by exact prefixLift 913801
  have htrace : WordTrace (prefixWord ++ tailWord_913801) baseStart_913801 baseEnd_913801 := by
    simpa [prefixWord, tailWord_913801, baseEnd_913801] using wordTrace_append hprefix tailTrace_913801
  have hstable : (prefixWord ++ tailWord_913801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913801).length < 2 ^ (prefixWord ++ tailWord_913801).sum := by decide
  have hdescent : baseEnd_913801 < baseStart_913801 := by decide
  rcases family_descends (prefixWord ++ tailWord_913801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913803 : List Nat := [1, 1, 1, 1, 4, 5, 2, 2, 1, 4]
def baseStart_913803 : Nat := 118140960795 + 913803 * 2 ^ 59
def prefixEnd_913803 : Nat := 4983230072969 + 3 ^ 40 * 913803 * 2
def baseEnd_913803 : Nat := 312813441680395650173335

theorem tailTrace_913803 : CollatzResearch.WordTrace tailWord_913803 prefixEnd_913803 312813441680395650173335 := by
  unfold tailWord_913803
  simp only [CollatzResearch.WordTrace]
  refine ⟨33329133508455270972530063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22219422338970180648353375 33329133508455270972530063)
  ·
    refine ⟨49993700262682906458795095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33329133508455270972530063 49993700262682906458795095)
    ·
      refine ⟨74990550394024359688192643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49993700262682906458795095 74990550394024359688192643)
      ·
        refine ⟨112485825591036539532288965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74990550394024359688192643 112485825591036539532288965)
        ·
          refine ⟨21091092298319351162304181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112485825591036539532288965 21091092298319351162304181)
          ·
            refine ⟨1977289902967439171466017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21091092298319351162304181 1977289902967439171466017)
            ·
              refine ⟨1482967427225579378599513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1977289902967439171466017 1482967427225579378599513)
              ·
                refine ⟨1112225570419184533949635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1482967427225579378599513 1112225570419184533949635)
                ·
                  refine ⟨1668338355628776800924453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1112225570419184533949635 1668338355628776800924453)
                  ·
                    refine ⟨312813441680395650173335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1668338355628776800924453 312813441680395650173335)
                    ·
                      rfl

theorem cell22_913803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 2, 1, 4].length) (baseStart_913803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_913803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_913803 prefixEnd_913803 := by exact prefixLift 913803
  have htrace : WordTrace (prefixWord ++ tailWord_913803) baseStart_913803 baseEnd_913803 := by
    simpa [prefixWord, tailWord_913803, baseEnd_913803] using wordTrace_append hprefix tailTrace_913803
  have hstable : (prefixWord ++ tailWord_913803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913803).length < 2 ^ (prefixWord ++ tailWord_913803).sum := by decide
  have hdescent : baseEnd_913803 < baseStart_913803 := by decide
  rcases family_descends (prefixWord ++ tailWord_913803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913940 : List Nat := [2, 4, 3, 1, 1, 1, 1, 2, 2, 5]
def baseStart_913940 : Nat := 118140960795 + 913940 * 2 ^ 59
def prefixEnd_913940 : Nat := 4983230072969 + 3 ^ 40 * 913940 * 2
def baseEnd_913940 : Nat := 312860339580172959497915

theorem tailTrace_913940 : CollatzResearch.WordTrace tailWord_913940 prefixEnd_913940 312860339580172959497915 := by
  unfold tailWord_913940
  simp only [CollatzResearch.WordTrace]
  refine ⟨16667065154479471685133637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22222753539305962246844849 16667065154479471685133637)
  ·
    refine ⟨3125074716464900940962557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16667065154479471685133637 3125074716464900940962557)
    ·
      refine ⟨1171903018674337852860959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3125074716464900940962557 1171903018674337852860959)
      ·
        refine ⟨1757854528011506779291439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1171903018674337852860959 1757854528011506779291439)
        ·
          refine ⟨2636781792017260168937159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1757854528011506779291439 2636781792017260168937159)
          ·
            refine ⟨3955172688025890253405739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2636781792017260168937159 3955172688025890253405739)
            ·
              refine ⟨5932759032038835380108609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3955172688025890253405739 5932759032038835380108609)
              ·
                refine ⟨4449569274029126535081457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5932759032038835380108609 4449569274029126535081457)
                ·
                  refine ⟨3337176955521844901311093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4449569274029126535081457 3337176955521844901311093)
                  ·
                    refine ⟨312860339580172959497915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3337176955521844901311093 312860339580172959497915)
                    ·
                      rfl

theorem cell22_913940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_913940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_913940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_913940 prefixEnd_913940 := by exact prefixLift 913940
  have htrace : WordTrace (prefixWord ++ tailWord_913940) baseStart_913940 baseEnd_913940 := by
    simpa [prefixWord, tailWord_913940, baseEnd_913940] using wordTrace_append hprefix tailTrace_913940
  have hstable : (prefixWord ++ tailWord_913940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913940).length < 2 ^ (prefixWord ++ tailWord_913940).sum := by decide
  have hdescent : baseEnd_913940 < baseStart_913940 := by decide
  rcases family_descends (prefixWord ++ tailWord_913940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913953 : List Nat := [1, 2, 3, 2, 2, 1, 4, 1, 6]
def baseStart_913953 : Nat := 118140960795 + 913953 * 2 ^ 59
def prefixEnd_913953 : Nat := 4983230072969 + 3 ^ 40 * 913953 * 2
def baseEnd_913953 : Nat := 104288263248615086307625

theorem tailTrace_913953 : CollatzResearch.WordTrace tailWord_913953 prefixEnd_913953 104288263248615086307625 := by
  unfold tailWord_913953
  simp only [CollatzResearch.WordTrace]
  refine ⟨33334604457911846590490513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22223069638607897726993675 33334604457911846590490513)
  ·
    refine ⟨25000953343433884942867885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33334604457911846590490513 25000953343433884942867885)
    ·
      refine ⟨9375357503787706853575457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25000953343433884942867885 9375357503787706853575457)
      ·
        refine ⟨7031518127840780140181593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9375357503787706853575457 7031518127840780140181593)
        ·
          refine ⟨5273638595880585105136195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7031518127840780140181593 5273638595880585105136195)
          ·
            refine ⟨7910457893820877657704293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5273638595880585105136195 7910457893820877657704293)
            ·
              refine ⟨1483210855091414560819555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7910457893820877657704293 1483210855091414560819555)
              ·
                refine ⟨2224816282637121841229333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1483210855091414560819555 2224816282637121841229333)
                ·
                  refine ⟨104288263248615086307625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2224816282637121841229333 104288263248615086307625)
                  ·
                    rfl

theorem cell22_913953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 1, 6].length) (baseStart_913953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_913953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_913953 prefixEnd_913953 := by exact prefixLift 913953
  have htrace : WordTrace (prefixWord ++ tailWord_913953) baseStart_913953 baseEnd_913953 := by
    simpa [prefixWord, tailWord_913953, baseEnd_913953] using wordTrace_append hprefix tailTrace_913953
  have hstable : (prefixWord ++ tailWord_913953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913953).length < 2 ^ (prefixWord ++ tailWord_913953).sum := by decide
  have hdescent : baseEnd_913953 < baseStart_913953 := by decide
  rcases family_descends (prefixWord ++ tailWord_913953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913959 : List Nat := [1, 1, 7, 2, 1, 1, 3, 1, 5]
def baseStart_913959 : Nat := 118140960795 + 913959 * 2 ^ 59
def prefixEnd_913959 : Nat := 4983230072969 + 3 ^ 40 * 913959 * 2
def baseEnd_913959 : Nat := 104288947889487747757619

theorem tailTrace_913959 : CollatzResearch.WordTrace tailWord_913959 prefixEnd_913959 104288947889487747757619 := by
  unfold tailWord_913959
  simp only [CollatzResearch.WordTrace]
  refine ⟨33334823295890109615208931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22223215530593406410139287 33334823295890109615208931)
  ·
    refine ⟨50002234943835164422813397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33334823295890109615208931 50002234943835164422813397)
    ·
      refine ⟨1171927381496136666159689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 50002234943835164422813397 1171927381496136666159689)
      ·
        refine ⟨878945536122102499619767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1171927381496136666159689 878945536122102499619767)
        ·
          refine ⟨1318418304183153749429651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 878945536122102499619767 1318418304183153749429651)
          ·
            refine ⟨1977627456274730624144477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1318418304183153749429651 1977627456274730624144477)
            ·
              refine ⟨741610296103023984054179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1977627456274730624144477 741610296103023984054179)
              ·
                refine ⟨1112415444154535976081269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 741610296103023984054179 1112415444154535976081269)
                ·
                  refine ⟨104288947889487747757619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1112415444154535976081269 104288947889487747757619)
                  ·
                    rfl

theorem cell22_913959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 1, 5].length) (baseStart_913959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_913959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_913959 prefixEnd_913959 := by exact prefixLift 913959
  have htrace : WordTrace (prefixWord ++ tailWord_913959) baseStart_913959 baseEnd_913959 := by
    simpa [prefixWord, tailWord_913959, baseEnd_913959] using wordTrace_append hprefix tailTrace_913959
  have hstable : (prefixWord ++ tailWord_913959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913959).length < 2 ^ (prefixWord ++ tailWord_913959).sum := by decide
  have hdescent : baseEnd_913959 < baseStart_913959 := by decide
  rcases family_descends (prefixWord ++ tailWord_913959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913968 : List Nat := [2, 1, 1, 1, 2, 3, 5, 1, 1, 5]
def baseStart_913968 : Nat := 118140960795 + 913968 * 2 ^ 59
def prefixEnd_913968 : Nat := 4983230072969 + 3 ^ 40 * 913968 * 2
def baseEnd_913968 : Nat := 312869924552390219797829

theorem tailTrace_913968 : CollatzResearch.WordTrace tailWord_913968 prefixEnd_913968 312869924552390219797829 := by
  unfold tailWord_913968
  simp only [CollatzResearch.WordTrace]
  refine ⟨16667575776428752076143279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22223434368571669434857705 16667575776428752076143279)
  ·
    refine ⟨25001363664643128114214919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16667575776428752076143279 25001363664643128114214919)
    ·
      refine ⟨37502045496964692171322379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25001363664643128114214919 37502045496964692171322379)
      ·
        refine ⟨56253068245447038256983569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37502045496964692171322379 56253068245447038256983569)
        ·
          refine ⟨42189801184085278692737677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56253068245447038256983569 42189801184085278692737677)
          ·
            refine ⟨15821175444031979509776629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42189801184085278692737677 15821175444031979509776629)
            ·
              refine ⟨1483235197877998079041559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15821175444031979509776629 1483235197877998079041559)
              ·
                refine ⟨2224852796816997118562339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1483235197877998079041559 2224852796816997118562339)
                ·
                  refine ⟨3337279195225495677843509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2224852796816997118562339 3337279195225495677843509)
                  ·
                    refine ⟨312869924552390219797829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3337279195225495677843509 312869924552390219797829)
                    ·
                      rfl

theorem cell22_913968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 1, 1, 5].length) (baseStart_913968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_913968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_913968 prefixEnd_913968 := by exact prefixLift 913968
  have htrace : WordTrace (prefixWord ++ tailWord_913968) baseStart_913968 baseEnd_913968 := by
    simpa [prefixWord, tailWord_913968, baseEnd_913968] using wordTrace_append hprefix tailTrace_913968
  have hstable : (prefixWord ++ tailWord_913968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913968).length < 2 ^ (prefixWord ++ tailWord_913968).sum := by decide
  have hdescent : baseEnd_913968 < baseStart_913968 := by decide
  rcases family_descends (prefixWord ++ tailWord_913968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913983 : List Nat := [1, 1, 2, 2, 3, 2, 2, 3, 2, 4]
def baseStart_913983 : Nat := 118140960795 + 913983 * 2 ^ 59
def prefixEnd_913983 : Nat := 4983230072969 + 3 ^ 40 * 913983 * 2
def baseEnd_913983 : Nat := 312875059358935180672783

theorem tailTrace_913983 : CollatzResearch.WordTrace tailWord_913983 prefixEnd_913983 312875059358935180672783 := by
  unfold tailWord_913983
  simp only [CollatzResearch.WordTrace]
  refine ⟨33335698647803161714082603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22223799098535441142721735 33335698647803161714082603)
  ·
    refine ⟨50003547971704742571123905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33335698647803161714082603 50003547971704742571123905)
    ·
      refine ⟨37502660978778556928342929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50003547971704742571123905 37502660978778556928342929)
      ·
        refine ⟨28126995734083917696257197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37502660978778556928342929 28126995734083917696257197)
        ·
          refine ⟨10547623400281469136096449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28126995734083917696257197 10547623400281469136096449)
          ·
            refine ⟨7910717550211101852072337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10547623400281469136096449 7910717550211101852072337)
            ·
              refine ⟨5933038162658326389054253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7910717550211101852072337 5933038162658326389054253)
              ·
                refine ⟨2224889310996872395895345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5933038162658326389054253 2224889310996872395895345)
                ·
                  refine ⟨1668666983247654296921509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2224889310996872395895345 1668666983247654296921509)
                  ·
                    refine ⟨312875059358935180672783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1668666983247654296921509 312875059358935180672783)
                    ·
                      rfl

theorem cell22_913983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3, 2, 4].length) (baseStart_913983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_913983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_913983 prefixEnd_913983 := by exact prefixLift 913983
  have htrace : WordTrace (prefixWord ++ tailWord_913983) baseStart_913983 baseEnd_913983 := by
    simpa [prefixWord, tailWord_913983, baseEnd_913983] using wordTrace_append hprefix tailTrace_913983
  have hstable : (prefixWord ++ tailWord_913983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913983).length < 2 ^ (prefixWord ++ tailWord_913983).sum := by decide
  have hdescent : baseEnd_913983 < baseStart_913983 := by decide
  rcases family_descends (prefixWord ++ tailWord_913983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_913985 : List Nat := [1, 2, 5, 1, 1, 2, 1, 2, 4, 3]
def baseStart_913985 : Nat := 118140960795 + 913985 * 2 ^ 59
def prefixEnd_913985 : Nat := 4983230072969 + 3 ^ 40 * 913985 * 2
def baseEnd_913985 : Nat := 312875743999807842122777

theorem tailTrace_913985 : CollatzResearch.WordTrace tailWord_913985 prefixEnd_913985 312875743999807842122777 := by
  unfold tailWord_913985
  simp only [CollatzResearch.WordTrace]
  refine ⟨33335771593795916055655409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22223847729197277370436939 33335771593795916055655409)
  ·
    refine ⟨25001828695346937041741557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33335771593795916055655409 25001828695346937041741557)
    ·
      refine ⟨2343921440188775347663271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25001828695346937041741557 2343921440188775347663271)
      ·
        refine ⟨3515882160283163021494907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2343921440188775347663271 3515882160283163021494907)
        ·
          refine ⟨5273823240424744532242361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3515882160283163021494907 5273823240424744532242361)
          ·
            refine ⟨3955367430318558399181771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5273823240424744532242361 3955367430318558399181771)
            ·
              refine ⟨5933051145477837598772657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3955367430318558399181771 5933051145477837598772657)
              ·
                refine ⟨4449788359108378199079493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5933051145477837598772657 4449788359108378199079493)
                ·
                  refine ⟨834335317332820912327405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4449788359108378199079493 834335317332820912327405)
                  ·
                    refine ⟨312875743999807842122777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 834335317332820912327405 312875743999807842122777)
                    ·
                      rfl

theorem cell22_913985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_913985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_913985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_913985 prefixEnd_913985 := by exact prefixLift 913985
  have htrace : WordTrace (prefixWord ++ tailWord_913985) baseStart_913985 baseEnd_913985 := by
    simpa [prefixWord, tailWord_913985, baseEnd_913985] using wordTrace_append hprefix tailTrace_913985
  have hstable : (prefixWord ++ tailWord_913985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_913985).length < 2 ^ (prefixWord ++ tailWord_913985).sum := by decide
  have hdescent : baseEnd_913985 < baseStart_913985 := by decide
  rcases family_descends (prefixWord ++ tailWord_913985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914073 : List Nat := [1, 2, 1, 2, 1, 2, 3, 1, 5, 4]
def baseStart_914073 : Nat := 118140960795 + 914073 * 2 ^ 59
def prefixEnd_914073 : Nat := 4983230072969 + 3 ^ 40 * 914073 * 2
def baseEnd_914073 : Nat := 312905868198204945922507

theorem tailTrace_914073 : CollatzResearch.WordTrace tailWord_914073 prefixEnd_914073 312905868198204945922507 := by
  unfold tailWord_914073
  simp only [CollatzResearch.WordTrace]
  refine ⟨33338981217477107084858873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22225987478318071389905915 33338981217477107084858873)
  ·
    refine ⟨25004235913107830313644155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33338981217477107084858873 25004235913107830313644155)
    ·
      refine ⟨37506353869661745470466233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25004235913107830313644155 37506353869661745470466233)
      ·
        refine ⟨28129765402246309102849675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37506353869661745470466233 28129765402246309102849675)
        ·
          refine ⟨42194648103369463654274513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28129765402246309102849675 42194648103369463654274513)
          ·
            refine ⟨31645986077527097740705885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42194648103369463654274513 31645986077527097740705885)
            ·
              refine ⟨11867244779072661652764707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31645986077527097740705885 11867244779072661652764707)
              ·
                refine ⟨17800867168608992479147061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11867244779072661652764707 17800867168608992479147061)
                ·
                  refine ⟨1668831297057093044920037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17800867168608992479147061 1668831297057093044920037)
                  ·
                    refine ⟨312905868198204945922507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1668831297057093044920037 312905868198204945922507)
                    ·
                      rfl

theorem cell22_914073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 5, 4].length) (baseStart_914073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_914073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_914073 prefixEnd_914073 := by exact prefixLift 914073
  have htrace : WordTrace (prefixWord ++ tailWord_914073) baseStart_914073 baseEnd_914073 := by
    simpa [prefixWord, tailWord_914073, baseEnd_914073] using wordTrace_append hprefix tailTrace_914073
  have hstable : (prefixWord ++ tailWord_914073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914073).length < 2 ^ (prefixWord ++ tailWord_914073).sum := by decide
  have hdescent : baseEnd_914073 < baseStart_914073 := by decide
  rcases family_descends (prefixWord ++ tailWord_914073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914122 : List Nat := [3, 1, 2, 1, 4, 1, 2, 4, 4]
def baseStart_914122 : Nat := 118140960795 + 914122 * 2 ^ 59
def prefixEnd_914122 : Nat := 4983230072969 + 3 ^ 40 * 914122 * 2
def baseEnd_914122 : Nat := 104307547299861717149119

theorem tailTrace_914122 : CollatzResearch.WordTrace tailWord_914122 prefixEnd_914122 104307547299861717149119 := by
  unfold tailWord_914122
  simp only [CollatzResearch.WordTrace]
  refine ⟨8335192098574897113348155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22227178929533058968928413 8335192098574897113348155)
  ·
    refine ⟨12502788147862345670022233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8335192098574897113348155 12502788147862345670022233)
    ·
      refine ⟨9377091110896759252516675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12502788147862345670022233 9377091110896759252516675)
      ·
        refine ⟨14065636666345138878775013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9377091110896759252516675 14065636666345138878775013)
        ·
          refine ⟨2637306874939713539770315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14065636666345138878775013 2637306874939713539770315)
          ·
            refine ⟨3955960312409570309655473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2637306874939713539770315 3955960312409570309655473)
            ·
              refine ⟨2966970234307177732241605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3955960312409570309655473 2966970234307177732241605)
              ·
                refine ⟨556306918932595824795301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2966970234307177732241605 556306918932595824795301)
                ·
                  refine ⟨104307547299861717149119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 556306918932595824795301 104307547299861717149119)
                  ·
                    rfl

theorem cell22_914122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 4, 4].length) (baseStart_914122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_914122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_914122 prefixEnd_914122 := by exact prefixLift 914122
  have htrace : WordTrace (prefixWord ++ tailWord_914122) baseStart_914122 baseEnd_914122 := by
    simpa [prefixWord, tailWord_914122, baseEnd_914122] using wordTrace_append hprefix tailTrace_914122
  have hstable : (prefixWord ++ tailWord_914122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914122).length < 2 ^ (prefixWord ++ tailWord_914122).sum := by decide
  have hdescent : baseEnd_914122 < baseStart_914122 := by decide
  rcases family_descends (prefixWord ++ tailWord_914122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914163 : List Nat := [1, 1, 1, 2, 2, 3, 1, 2, 1, 8]
def baseStart_914163 : Nat := 118140960795 + 914163 * 2 ^ 59
def prefixEnd_914163 : Nat := 4983230072969 + 3 ^ 40 * 914163 * 2
def baseEnd_914163 : Nat := 312936677037474711172231

theorem tailTrace_914163 : CollatzResearch.WordTrace tailWord_914163 prefixEnd_914163 312936677037474711172231 := by
  unfold tailWord_914163
  simp only [CollatzResearch.WordTrace]
  refine ⟨33342263787151052455635143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22228175858100701637090095 33342263787151052455635143)
  ·
    refine ⟨50013395680726578683452715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33342263787151052455635143 50013395680726578683452715)
    ·
      refine ⟨75020093521089868025179073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50013395680726578683452715 75020093521089868025179073)
      ·
        refine ⟨56265070140817401018884305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75020093521089868025179073 56265070140817401018884305)
        ·
          refine ⟨42198802605613050764163229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56265070140817401018884305 42198802605613050764163229)
          ·
            refine ⟨15824550977104894036561211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42198802605613050764163229 15824550977104894036561211)
            ·
              refine ⟨23736826465657341054841817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15824550977104894036561211 23736826465657341054841817)
              ·
                refine ⟨17802619849243005791131363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23736826465657341054841817 17802619849243005791131363)
                ·
                  refine ⟨26703929773864508686697045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17802619849243005791131363 26703929773864508686697045)
                  ·
                    refine ⟨312936677037474711172231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 26703929773864508686697045 312936677037474711172231)
                    ·
                      rfl

theorem cell22_914163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 8].length) (baseStart_914163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_914163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_914163 prefixEnd_914163 := by exact prefixLift 914163
  have htrace : WordTrace (prefixWord ++ tailWord_914163) baseStart_914163 baseEnd_914163 := by
    simpa [prefixWord, tailWord_914163, baseEnd_914163] using wordTrace_append hprefix tailTrace_914163
  have hstable : (prefixWord ++ tailWord_914163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914163).length < 2 ^ (prefixWord ++ tailWord_914163).sum := by decide
  have hdescent : baseEnd_914163 < baseStart_914163 := by decide
  rcases family_descends (prefixWord ++ tailWord_914163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914180 : List Nat := [2, 3, 2, 2, 1, 1, 2, 1, 2, 6]
def baseStart_914180 : Nat := 118140960795 + 914180 * 2 ^ 59
def prefixEnd_914180 : Nat := 4983230072969 + 3 ^ 40 * 914180 * 2
def baseEnd_914180 : Nat := 312942496484892333497179

theorem tailTrace_914180 : CollatzResearch.WordTrace tailWord_914180 prefixEnd_914180 312942496484892333497179 := by
  unfold tailWord_914180
  simp only [CollatzResearch.WordTrace]
  refine ⟨16671441914044732179501997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22228589218726309572669329 16671441914044732179501997)
  ·
    refine ⟨6251790717766774567313249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16671441914044732179501997 6251790717766774567313249)
    ·
      refine ⟨4688843038325080925484937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6251790717766774567313249 4688843038325080925484937)
      ·
        refine ⟨3516632278743810694113703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4688843038325080925484937 3516632278743810694113703)
        ·
          refine ⟨5274948418115716041170555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3516632278743810694113703 5274948418115716041170555)
          ·
            refine ⟨7912422627173574061755833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5274948418115716041170555 7912422627173574061755833)
            ·
              refine ⟨5934316970380180546316875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7912422627173574061755833 5934316970380180546316875)
              ·
                refine ⟨8901475455570270819475313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5934316970380180546316875 8901475455570270819475313)
                ·
                  refine ⟨6676106591677703114606485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8901475455570270819475313 6676106591677703114606485)
                  ·
                    refine ⟨312942496484892333497179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6676106591677703114606485 312942496484892333497179)
                    ·
                      rfl

theorem cell22_914180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_914180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_914180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_914180 prefixEnd_914180 := by exact prefixLift 914180
  have htrace : WordTrace (prefixWord ++ tailWord_914180) baseStart_914180 baseEnd_914180 := by
    simpa [prefixWord, tailWord_914180, baseEnd_914180] using wordTrace_append hprefix tailTrace_914180
  have hstable : (prefixWord ++ tailWord_914180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914180).length < 2 ^ (prefixWord ++ tailWord_914180).sum := by decide
  have hdescent : baseEnd_914180 < baseStart_914180 := by decide
  rcases family_descends (prefixWord ++ tailWord_914180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914195 : List Nat := [1, 1, 1, 2, 1, 3, 5, 3, 5]
def baseStart_914195 : Nat := 118140960795 + 914195 * 2 ^ 59
def prefixEnd_914195 : Nat := 4983230072969 + 3 ^ 40 * 914195 * 2
def baseEnd_914195 : Nat := 104315877097145764790711

theorem tailTrace_914195 : CollatzResearch.WordTrace tailWord_914195 prefixEnd_914195 104315877097145764790711 := by
  unfold tailWord_914195
  simp only [CollatzResearch.WordTrace]
  refine ⟨33343430923035121920800039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22228953948690081280533359 33343430923035121920800039)
  ·
    refine ⟨50015146384552682881200059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33343430923035121920800039 50015146384552682881200059)
    ·
      refine ⟨75022719576829024321800089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50015146384552682881200059 75022719576829024321800089)
      ·
        refine ⟨56267039682621768241350067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75022719576829024321800089 56267039682621768241350067)
        ·
          refine ⟨84400559523932652362025101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56267039682621768241350067 84400559523932652362025101)
          ·
            refine ⟨31650209821474744635759413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84400559523932652362025101 31650209821474744635759413)
            ·
              refine ⟨2967207170763257309602445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31650209821474744635759413 2967207170763257309602445)
              ·
                refine ⟨1112702689036221491100917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2967207170763257309602445 1112702689036221491100917)
                ·
                  refine ⟨104315877097145764790711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1112702689036221491100917 104315877097145764790711)
                  ·
                    rfl

theorem cell22_914195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 3, 5].length) (baseStart_914195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_914195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_914195 prefixEnd_914195 := by exact prefixLift 914195
  have htrace : WordTrace (prefixWord ++ tailWord_914195) baseStart_914195 baseEnd_914195 := by
    simpa [prefixWord, tailWord_914195, baseEnd_914195] using wordTrace_append hprefix tailTrace_914195
  have hstable : (prefixWord ++ tailWord_914195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914195).length < 2 ^ (prefixWord ++ tailWord_914195).sum := by decide
  have hdescent : baseEnd_914195 < baseStart_914195 := by decide
  rcases family_descends (prefixWord ++ tailWord_914195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914257 : List Nat := [1, 2, 2, 1, 6, 1, 1, 2, 6]
def baseStart_914257 : Nat := 118140960795 + 914257 * 2 ^ 59
def prefixEnd_914257 : Nat := 4983230072969 + 3 ^ 40 * 914257 * 2
def baseEnd_914257 : Nat := 104322951719496599773981

theorem tailTrace_914257 : CollatzResearch.WordTrace tailWord_914257 prefixEnd_914257 104322951719496599773981 := by
  unfold tailWord_914257
  simp only [CollatzResearch.WordTrace]
  refine ⟨33345692248810506509557025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22230461499207004339704683 33345692248810506509557025)
  ·
    refine ⟨25009269186607879882167769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33345692248810506509557025 25009269186607879882167769)
    ·
      refine ⟨18756951889955909911625827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25009269186607879882167769 18756951889955909911625827)
      ·
        refine ⟨28135427834933864867438741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18756951889955909911625827 28135427834933864867438741)
        ·
          refine ⟨1318848179762524915661191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 28135427834933864867438741 1318848179762524915661191)
          ·
            refine ⟨1978272269643787373491787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1318848179762524915661191 1978272269643787373491787)
            ·
              refine ⟨2967408404465681060237681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1978272269643787373491787 2967408404465681060237681)
              ·
                refine ⟨2225556303349260795178261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2967408404465681060237681 2225556303349260795178261)
                ·
                  refine ⟨104322951719496599773981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2225556303349260795178261 104322951719496599773981)
                  ·
                    rfl

theorem cell22_914257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 2, 6].length) (baseStart_914257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_914257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_914257 prefixEnd_914257 := by exact prefixLift 914257
  have htrace : WordTrace (prefixWord ++ tailWord_914257) baseStart_914257 baseEnd_914257 := by
    simpa [prefixWord, tailWord_914257, baseEnd_914257] using wordTrace_append hprefix tailTrace_914257
  have hstable : (prefixWord ++ tailWord_914257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914257).length < 2 ^ (prefixWord ++ tailWord_914257).sum := by decide
  have hdescent : baseEnd_914257 < baseStart_914257 := by decide
  rcases family_descends (prefixWord ++ tailWord_914257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914272 : List Nat := [2, 1, 1, 3, 3, 1, 2, 2, 4, 3]
def baseStart_914272 : Nat := 118140960795 + 914272 * 2 ^ 59
def prefixEnd_914272 : Nat := 4983230072969 + 3 ^ 40 * 914272 * 2
def baseEnd_914272 : Nat := 312973989965034760196897

theorem tailTrace_914272 : CollatzResearch.WordTrace tailWord_914272 prefixEnd_914272 312973989965034760196897 := by
  unfold tailWord_914272
  simp only [CollatzResearch.WordTrace]
  refine ⟨16673119671878082035676535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22230826229170776047568713 16673119671878082035676535)
  ·
    refine ⟨25009679507817123053514803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16673119671878082035676535 25009679507817123053514803)
    ·
      refine ⟨37514519261725684580272205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25009679507817123053514803 37514519261725684580272205)
      ·
        refine ⟨14067944723147131717602077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37514519261725684580272205 14067944723147131717602077)
        ·
          refine ⟨5275479271180174394100779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14067944723147131717602077 5275479271180174394100779)
          ·
            refine ⟨7913218906770261591151169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5275479271180174394100779 7913218906770261591151169)
            ·
              refine ⟨5934914180077696193363377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7913218906770261591151169 5934914180077696193363377)
              ·
                refine ⟨4451185635058272145022533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5934914180077696193363377 4451185635058272145022533)
                ·
                  refine ⟨834597306573426027191725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4451185635058272145022533 834597306573426027191725)
                  ·
                    refine ⟨312973989965034760196897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 834597306573426027191725 312973989965034760196897)
                    ·
                      rfl

theorem cell22_914272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 4, 3].length) (baseStart_914272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_914272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_914272 prefixEnd_914272 := by exact prefixLift 914272
  have htrace : WordTrace (prefixWord ++ tailWord_914272) baseStart_914272 baseEnd_914272 := by
    simpa [prefixWord, tailWord_914272, baseEnd_914272] using wordTrace_append hprefix tailTrace_914272
  have hstable : (prefixWord ++ tailWord_914272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914272).length < 2 ^ (prefixWord ++ tailWord_914272).sum := by decide
  have hdescent : baseEnd_914272 < baseStart_914272 := by decide
  rcases family_descends (prefixWord ++ tailWord_914272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914276 : List Nat := [2, 3, 1, 1, 4, 3, 2, 1, 1, 4]
def baseStart_914276 : Nat := 118140960795 + 914276 * 2 ^ 59
def prefixEnd_914276 : Nat := 4983230072969 + 3 ^ 40 * 914276 * 2
def baseEnd_914276 : Nat := 312975359246780083096885

theorem tailTrace_914276 : CollatzResearch.WordTrace tailWord_914276 prefixEnd_914276 312975359246780083096885 := by
  unfold tailWord_914276
  simp only [CollatzResearch.WordTrace]
  refine ⟨16673192617870836377249341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22230923490494448502999121 16673192617870836377249341)
  ·
    refine ⟨6252447231701563641468503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16673192617870836377249341 6252447231701563641468503)
    ·
      refine ⟨9378670847552345462202755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6252447231701563641468503 9378670847552345462202755)
      ·
        refine ⟨14068006271328518193304133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9378670847552345462202755 14068006271328518193304133)
        ·
          refine ⟨2637751175874097161244525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14068006271328518193304133 2637751175874097161244525)
          ·
            refine ⟨989156690952786435466697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2637751175874097161244525 989156690952786435466697)
            ·
              refine ⟨741867518214589826600023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 989156690952786435466697 741867518214589826600023)
              ·
                refine ⟨1112801277321884739900035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 741867518214589826600023 1112801277321884739900035)
                ·
                  refine ⟨1669201915982827109850053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1112801277321884739900035 1669201915982827109850053)
                  ·
                    refine ⟨312975359246780083096885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1669201915982827109850053 312975359246780083096885)
                    ·
                      rfl

theorem cell22_914276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 1, 1, 4].length) (baseStart_914276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_914276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_914276 prefixEnd_914276 := by exact prefixLift 914276
  have htrace : WordTrace (prefixWord ++ tailWord_914276) baseStart_914276 baseEnd_914276 := by
    simpa [prefixWord, tailWord_914276, baseEnd_914276] using wordTrace_append hprefix tailTrace_914276
  have hstable : (prefixWord ++ tailWord_914276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914276).length < 2 ^ (prefixWord ++ tailWord_914276).sum := by decide
  have hdescent : baseEnd_914276 < baseStart_914276 := by decide
  rcases family_descends (prefixWord ++ tailWord_914276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914289 : List Nat := [1, 2, 2, 2, 1, 4, 3, 2, 2, 3]
def baseStart_914289 : Nat := 118140960795 + 914289 * 2 ^ 59
def prefixEnd_914289 : Nat := 4983230072969 + 3 ^ 40 * 914289 * 2
def baseEnd_914289 : Nat := 312979809412452382521845

theorem tailTrace_914289 : CollatzResearch.WordTrace tailWord_914289 prefixEnd_914289 312979809412452382521845 := by
  unfold tailWord_914289
  simp only [CollatzResearch.WordTrace]
  refine ⟨33346859384694575974721921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22231239589796383983147947 33346859384694575974721921)
  ·
    refine ⟨25010144538520931981041441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33346859384694575974721921 25010144538520931981041441)
    ·
      refine ⟨18757608403890698985781081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25010144538520931981041441 18757608403890698985781081)
      ·
        refine ⟨14068206302918024239335811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18757608403890698985781081 14068206302918024239335811)
        ·
          refine ⟨21102309454377036359003717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14068206302918024239335811 21102309454377036359003717)
          ·
            refine ⟨3956683022695694317313197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21102309454377036359003717 3956683022695694317313197)
            ·
              refine ⟨1483756133510885368992449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3956683022695694317313197 1483756133510885368992449)
              ·
                refine ⟨1112817100133164026744337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1483756133510885368992449 1112817100133164026744337)
                ·
                  refine ⟨834612825099873020058253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1112817100133164026744337 834612825099873020058253)
                  ·
                    refine ⟨312979809412452382521845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 834612825099873020058253 312979809412452382521845)
                    ·
                      rfl

theorem cell22_914289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 2, 2, 3].length) (baseStart_914289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_914289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_914289 prefixEnd_914289 := by exact prefixLift 914289
  have htrace : WordTrace (prefixWord ++ tailWord_914289) baseStart_914289 baseEnd_914289 := by
    simpa [prefixWord, tailWord_914289, baseEnd_914289] using wordTrace_append hprefix tailTrace_914289
  have hstable : (prefixWord ++ tailWord_914289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914289).length < 2 ^ (prefixWord ++ tailWord_914289).sum := by decide
  have hdescent : baseEnd_914289 < baseStart_914289 := by decide
  rcases family_descends (prefixWord ++ tailWord_914289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914315 : List Nat := [1, 1, 1, 1, 4, 2, 2, 2, 2, 6]
def baseStart_914315 : Nat := 118140960795 + 914315 * 2 ^ 59
def prefixEnd_914315 : Nat := 4983230072969 + 3 ^ 40 * 914315 * 2
def baseEnd_914315 : Nat := 312988709743796981371765

theorem tailTrace_914315 : CollatzResearch.WordTrace tailWord_914315 prefixEnd_914315 312988709743796981371765 := by
  unfold tailWord_914315
  simp only [CollatzResearch.WordTrace]
  refine ⟨33347807682600382415168399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22231871788400254943445599 33347807682600382415168399)
  ·
    refine ⟨50021711523900573622752599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33347807682600382415168399 50021711523900573622752599)
    ·
      refine ⟨75032567285850860434128899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50021711523900573622752599 75032567285850860434128899)
      ·
        refine ⟨112548850928776290651193349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75032567285850860434128899 112548850928776290651193349)
        ·
          refine ⟨21102909549145554497098753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112548850928776290651193349 21102909549145554497098753)
          ·
            refine ⟨15827182161859165872824065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21102909549145554497098753 15827182161859165872824065)
            ·
              refine ⟨11870386621394374404618049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15827182161859165872824065 11870386621394374404618049)
              ·
                refine ⟨8902789966045780803463537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11870386621394374404618049 8902789966045780803463537)
                ·
                  refine ⟨6677092474534335602597653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8902789966045780803463537 6677092474534335602597653)
                  ·
                    refine ⟨312988709743796981371765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6677092474534335602597653 312988709743796981371765)
                    ·
                      rfl

theorem cell22_914315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 6].length) (baseStart_914315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_914315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_914315 prefixEnd_914315 := by exact prefixLift 914315
  have htrace : WordTrace (prefixWord ++ tailWord_914315) baseStart_914315 baseEnd_914315 := by
    simpa [prefixWord, tailWord_914315, baseEnd_914315] using wordTrace_append hprefix tailTrace_914315
  have hstable : (prefixWord ++ tailWord_914315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914315).length < 2 ^ (prefixWord ++ tailWord_914315).sum := by decide
  have hdescent : baseEnd_914315 < baseStart_914315 := by decide
  rcases family_descends (prefixWord ++ tailWord_914315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914402 : List Nat := [3, 3, 3, 1, 1, 3, 2, 2, 1, 3]
def baseStart_914402 : Nat := 118140960795 + 914402 * 2 ^ 59
def prefixEnd_914402 : Nat := 4983230072969 + 3 ^ 40 * 914402 * 2
def baseEnd_914402 : Nat := 313018491621757754446499

theorem tailTrace_914402 : CollatzResearch.WordTrace tailWord_914402 prefixEnd_914402 313018491621757754446499 := by
  unfold tailWord_914402
  simp only [CollatzResearch.WordTrace]
  refine ⟨8337745208321299068396365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22233987222190130849056973 8337745208321299068396365)
  ·
    refine ⟨3126654453120487150648637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8337745208321299068396365 3126654453120487150648637)
    ·
      refine ⟨1172495419920182681493239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3126654453120487150648637 1172495419920182681493239)
      ·
        refine ⟨1758743129880274022239859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1172495419920182681493239 1758743129880274022239859)
        ·
          refine ⟨2638114694820411033359789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1758743129880274022239859 2638114694820411033359789)
          ·
            refine ⟨989293010557654137509921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2638114694820411033359789 989293010557654137509921)
            ·
              refine ⟨741969757918240603132441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 989293010557654137509921 741969757918240603132441)
              ·
                refine ⟨556477318438680452349331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 741969757918240603132441 556477318438680452349331)
                ·
                  refine ⟨834715977658020678523997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 556477318438680452349331 834715977658020678523997)
                  ·
                    refine ⟨313018491621757754446499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 834715977658020678523997 313018491621757754446499)
                    ·
                      rfl

theorem cell22_914402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_914402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_914402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_914402 prefixEnd_914402 := by exact prefixLift 914402
  have htrace : WordTrace (prefixWord ++ tailWord_914402) baseStart_914402 baseEnd_914402 := by
    simpa [prefixWord, tailWord_914402, baseEnd_914402] using wordTrace_append hprefix tailTrace_914402
  have hstable : (prefixWord ++ tailWord_914402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914402).length < 2 ^ (prefixWord ++ tailWord_914402).sum := by decide
  have hdescent : baseEnd_914402 < baseStart_914402 := by decide
  rcases family_descends (prefixWord ++ tailWord_914402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914503 : List Nat := [1, 1, 4, 1, 3, 2, 3, 3, 1, 3]
def baseStart_914503 : Nat := 118140960795 + 914503 * 2 ^ 59
def prefixEnd_914503 : Nat := 4983230072969 + 3 ^ 40 * 914503 * 2
def baseEnd_914503 : Nat := 313053065985827157671189

theorem tailTrace_914503 : CollatzResearch.WordTrace tailWord_914503 prefixEnd_914503 313053065985827157671189 := by
  unfold tailWord_914503
  simp only [CollatzResearch.WordTrace]
  refine ⟨33354664605919290523012163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22236443070612860348674775 33354664605919290523012163)
  ·
    refine ⟨50031996908878935784518245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33354664605919290523012163 50031996908878935784518245)
    ·
      refine ⟨9380999420414800459597171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50031996908878935784518245 9380999420414800459597171)
      ·
        refine ⟨14071499130622200689395757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9380999420414800459597171 14071499130622200689395757)
        ·
          refine ⟨5276812173983325258523409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14071499130622200689395757 5276812173983325258523409)
          ·
            refine ⟨3957609130487493943892557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5276812173983325258523409 3957609130487493943892557)
            ·
              refine ⟨1484103423932810228959709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3957609130487493943892557 1484103423932810228959709)
              ·
                refine ⟨556538783974803835859891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1484103423932810228959709 556538783974803835859891)
                ·
                  refine ⟨834808175962205753789837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 556538783974803835859891 834808175962205753789837)
                  ·
                    refine ⟨313053065985827157671189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 834808175962205753789837 313053065985827157671189)
                    ·
                      rfl

theorem cell22_914503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 3, 1, 3].length) (baseStart_914503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_914503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_914503 prefixEnd_914503 := by exact prefixLift 914503
  have htrace : WordTrace (prefixWord ++ tailWord_914503) baseStart_914503 baseEnd_914503 := by
    simpa [prefixWord, tailWord_914503, baseEnd_914503] using wordTrace_append hprefix tailTrace_914503
  have hstable : (prefixWord ++ tailWord_914503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914503).length < 2 ^ (prefixWord ++ tailWord_914503).sum := by decide
  have hdescent : baseEnd_914503 < baseStart_914503 := by decide
  rcases family_descends (prefixWord ++ tailWord_914503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914578 : List Nat := [3, 2, 3, 1, 1, 3, 1, 4, 4]
def baseStart_914578 : Nat := 118140960795 + 914578 * 2 ^ 59
def prefixEnd_914578 : Nat := 4983230072969 + 3 ^ 40 * 914578 * 2
def baseEnd_914578 : Nat := 104359580006183987348653

theorem tailTrace_914578 : CollatzResearch.WordTrace tailWord_914578 prefixEnd_914578 104359580006183987348653 := by
  unfold tailWord_914578
  simp only [CollatzResearch.WordTrace]
  refine ⟨8339350020161894582998097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22238266720431718887994925 8339350020161894582998097)
  ·
    refine ⟨6254512515121420937248573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8339350020161894582998097 6254512515121420937248573)
    ·
      refine ⟨2345442193170532851468215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6254512515121420937248573 2345442193170532851468215)
      ·
        refine ⟨3518163289755799277202323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2345442193170532851468215 3518163289755799277202323)
        ·
          refine ⟨5277244934633698915803485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3518163289755799277202323 5277244934633698915803485)
          ·
            refine ⟨1978966850487637093426307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5277244934633698915803485 1978966850487637093426307)
            ·
              refine ⟨2968450275731455640139461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1978966850487637093426307 2968450275731455640139461)
              ·
                refine ⟨556584426699647932526149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2968450275731455640139461 556584426699647932526149)
                ·
                  refine ⟨104359580006183987348653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 556584426699647932526149 104359580006183987348653)
                  ·
                    rfl

theorem cell22_914578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 4, 4].length) (baseStart_914578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_914578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_914578 prefixEnd_914578 := by exact prefixLift 914578
  have htrace : WordTrace (prefixWord ++ tailWord_914578) baseStart_914578 baseEnd_914578 := by
    simpa [prefixWord, tailWord_914578, baseEnd_914578] using wordTrace_append hprefix tailTrace_914578
  have hstable : (prefixWord ++ tailWord_914578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914578).length < 2 ^ (prefixWord ++ tailWord_914578).sum := by decide
  have hdescent : baseEnd_914578 < baseStart_914578 := by decide
  rcases family_descends (prefixWord ++ tailWord_914578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914614 : List Nat := [5, 1, 3, 2, 1, 2, 2, 1, 1, 4]
def baseStart_914614 : Nat := 118140960795 + 914614 * 2 ^ 59
def prefixEnd_914614 : Nat := 4983230072969 + 3 ^ 40 * 914614 * 2
def baseEnd_914614 : Nat := 313091063554259868145849

theorem tailTrace_914614 : CollatzResearch.WordTrace tailWord_914614 prefixEnd_914614 313091063554259868145849 := by
  unfold tailWord_914614
  simp only [CollatzResearch.WordTrace]
  refine ⟨2084919569282322280018931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22239142072344770986868597 2084919569282322280018931)
  ·
    refine ⟨3127379353923483420028397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2084919569282322280018931 3127379353923483420028397)
    ·
      refine ⟨1172767257721306282510649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3127379353923483420028397 1172767257721306282510649)
      ·
        refine ⟨879575443290979711882987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1172767257721306282510649 879575443290979711882987)
        ·
          refine ⟨1319363164936469567824481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 879575443290979711882987 1319363164936469567824481)
          ·
            refine ⟨989522373702352175868361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1319363164936469567824481 989522373702352175868361)
            ·
              refine ⟨742141780276764131901271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 989522373702352175868361 742141780276764131901271)
              ·
                refine ⟨1113212670415146197851907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 742141780276764131901271 1113212670415146197851907)
                ·
                  refine ⟨1669819005622719296777861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1113212670415146197851907 1669819005622719296777861)
                  ·
                    refine ⟨313091063554259868145849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1669819005622719296777861 313091063554259868145849)
                    ·
                      rfl

theorem cell22_914614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_914614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_914614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_914614 prefixEnd_914614 := by exact prefixLift 914614
  have htrace : WordTrace (prefixWord ++ tailWord_914614) baseStart_914614 baseEnd_914614 := by
    simpa [prefixWord, tailWord_914614, baseEnd_914614] using wordTrace_append hprefix tailTrace_914614
  have hstable : (prefixWord ++ tailWord_914614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914614).length < 2 ^ (prefixWord ++ tailWord_914614).sum := by decide
  have hdescent : baseEnd_914614 < baseStart_914614 := by decide
  rcases family_descends (prefixWord ++ tailWord_914614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914681 : List Nat := [1, 2, 1, 3, 1, 1, 3, 5, 1, 4]
def baseStart_914681 : Nat := 118140960795 + 914681 * 2 ^ 59
def prefixEnd_914681 : Nat := 4983230072969 + 3 ^ 40 * 914681 * 2
def baseEnd_914681 : Nat := 313113999023494026720643

theorem tailTrace_914681 : CollatzResearch.WordTrace tailWord_914681 prefixEnd_914681 313113999023494026720643 := by
  unfold tailWord_914681
  simp only [CollatzResearch.WordTrace]
  refine ⟨33361156799274426922991897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22240771199516284615327931 33361156799274426922991897)
  ·
    refine ⟨25020867599455820192243923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33361156799274426922991897 25020867599455820192243923)
    ·
      refine ⟨37531301399183730288365885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25020867599455820192243923 37531301399183730288365885)
      ·
        refine ⟨14074238024693898858137207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37531301399183730288365885 14074238024693898858137207)
        ·
          refine ⟨21111357037040848287205811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14074238024693898858137207 21111357037040848287205811)
          ·
            refine ⟨31667035555561272430808717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21111357037040848287205811 31667035555561272430808717)
            ·
              refine ⟨11875138333335477161553269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31667035555561272430808717 11875138333335477161553269)
              ·
                refine ⟨1113294218750200983895619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11875138333335477161553269 1113294218750200983895619)
                ·
                  refine ⟨1669941328125301475843429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1113294218750200983895619 1669941328125301475843429)
                  ·
                    refine ⟨313113999023494026720643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1669941328125301475843429 313113999023494026720643)
                    ·
                      rfl

theorem cell22_914681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 5, 1, 4].length) (baseStart_914681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_914681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_914681 prefixEnd_914681 := by exact prefixLift 914681
  have htrace : WordTrace (prefixWord ++ tailWord_914681) baseStart_914681 baseEnd_914681 := by
    simpa [prefixWord, tailWord_914681, baseEnd_914681] using wordTrace_append hprefix tailTrace_914681
  have hstable : (prefixWord ++ tailWord_914681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914681).length < 2 ^ (prefixWord ++ tailWord_914681).sum := by decide
  have hdescent : baseEnd_914681 < baseStart_914681 := by decide
  rcases family_descends (prefixWord ++ tailWord_914681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914711 : List Nat := [1, 1, 3, 4, 1, 1, 2, 3, 1, 5]
def baseStart_914711 : Nat := 118140960795 + 914711 * 2 ^ 59
def prefixEnd_914711 : Nat := 4983230072969 + 3 ^ 40 * 914711 * 2
def baseEnd_914711 : Nat := 313124268636583948470551

theorem tailTrace_914711 : CollatzResearch.WordTrace tailWord_914711 prefixEnd_914711 313124268636583948470551 := by
  unfold tailWord_914711
  simp only [CollatzResearch.WordTrace]
  refine ⟨33362250989165742046583987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22241500659443828031055991 33362250989165742046583987)
  ·
    refine ⟨50043376483748613069875981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33362250989165742046583987 50043376483748613069875981)
    ·
      refine ⟨18766266181405729901203493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50043376483748613069875981 18766266181405729901203493)
      ·
        refine ⟨3518674909013574356475655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18766266181405729901203493 3518674909013574356475655)
        ·
          refine ⟨5278012363520361534713483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3518674909013574356475655 5278012363520361534713483)
          ·
            refine ⟨7917018545280542302070225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5278012363520361534713483 7917018545280542302070225)
            ·
              refine ⟨5937763908960406726552669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7917018545280542302070225 5937763908960406726552669)
              ·
                refine ⟨2226661465860152522457251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5937763908960406726552669 2226661465860152522457251)
                ·
                  refine ⟨3339992198790228783685877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2226661465860152522457251 3339992198790228783685877)
                  ·
                    refine ⟨313124268636583948470551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3339992198790228783685877 313124268636583948470551)
                    ·
                      rfl

theorem cell22_914711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3, 1, 5].length) (baseStart_914711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_914711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_914711 prefixEnd_914711 := by exact prefixLift 914711
  have htrace : WordTrace (prefixWord ++ tailWord_914711) baseStart_914711 baseEnd_914711 := by
    simpa [prefixWord, tailWord_914711, baseEnd_914711] using wordTrace_append hprefix tailTrace_914711
  have hstable : (prefixWord ++ tailWord_914711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914711).length < 2 ^ (prefixWord ++ tailWord_914711).sum := by decide
  have hdescent : baseEnd_914711 < baseStart_914711 := by decide
  rcases family_descends (prefixWord ++ tailWord_914711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914728 : List Nat := [2, 1, 5, 1, 2, 2, 1, 2, 1, 5]
def baseStart_914728 : Nat := 118140960795 + 914728 * 2 ^ 59
def prefixEnd_914728 : Nat := 4983230072969 + 3 ^ 40 * 914728 * 2
def baseEnd_914728 : Nat := 313130088084001570795499

theorem tailTrace_914728 : CollatzResearch.WordTrace tailWord_914728 prefixEnd_914728 313130088084001570795499 := by
  unfold tailWord_914728
  simp only [CollatzResearch.WordTrace]
  refine ⟨16681435515052076974976419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22241914020069435966635225 16681435515052076974976419)
  ·
    refine ⟨25022153272578115462464629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16681435515052076974976419 25022153272578115462464629)
    ·
      refine ⟨2345826869304198324606059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25022153272578115462464629 2345826869304198324606059)
      ·
        refine ⟨3518740303956297486909089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2345826869304198324606059 3518740303956297486909089)
        ·
          refine ⟨2639055227967223115181817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3518740303956297486909089 2639055227967223115181817)
          ·
            refine ⟨1979291420975417336386363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2639055227967223115181817 1979291420975417336386363)
            ·
              refine ⟨2968937131463126004579545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1979291420975417336386363 2968937131463126004579545)
              ·
                refine ⟨2226702848597344503434659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2968937131463126004579545 2226702848597344503434659)
                ·
                  refine ⟨3340054272896016755151989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2226702848597344503434659 3340054272896016755151989)
                  ·
                    refine ⟨313130088084001570795499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3340054272896016755151989 313130088084001570795499)
                    ·
                      rfl

theorem cell22_914728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_914728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_914728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_914728 prefixEnd_914728 := by exact prefixLift 914728
  have htrace : WordTrace (prefixWord ++ tailWord_914728) baseStart_914728 baseEnd_914728 := by
    simpa [prefixWord, tailWord_914728, baseEnd_914728] using wordTrace_append hprefix tailTrace_914728
  have hstable : (prefixWord ++ tailWord_914728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914728).length < 2 ^ (prefixWord ++ tailWord_914728).sum := by decide
  have hdescent : baseEnd_914728 < baseStart_914728 := by decide
  rcases family_descends (prefixWord ++ tailWord_914728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914773 : List Nat := [1, 3, 2, 2, 3, 1, 1, 1, 5, 3]
def baseStart_914773 : Nat := 118140960795 + 914773 * 2 ^ 59
def prefixEnd_914773 : Nat := 4983230072969 + 3 ^ 40 * 914773 * 2
def baseEnd_914773 : Nat := 313145492503636453420361

theorem tailTrace_914773 : CollatzResearch.WordTrace tailWord_914773 prefixEnd_914773 313145492503636453420361 := by
  unfold tailWord_914773
  simp only [CollatzResearch.WordTrace]
  refine ⟨33364512314941126635340973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22243008209960751090227315 33364512314941126635340973)
  ·
    refine ⟨12511692118102922488252865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33364512314941126635340973 12511692118102922488252865)
    ·
      refine ⟨9383769088577191866189649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12511692118102922488252865 9383769088577191866189649)
      ·
        refine ⟨7037826816432893899642237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9383769088577191866189649 7037826816432893899642237)
        ·
          refine ⟨2639185056162335212365839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7037826816432893899642237 2639185056162335212365839)
          ·
            refine ⟨3958777584243502818548759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2639185056162335212365839 3958777584243502818548759)
            ·
              refine ⟨5938166376365254227823139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3958777584243502818548759 5938166376365254227823139)
              ·
                refine ⟨8907249564547881341734709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5938166376365254227823139 8907249564547881341734709)
                ·
                  refine ⟨835054646676363875787629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8907249564547881341734709 835054646676363875787629)
                  ·
                    refine ⟨313145492503636453420361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 835054646676363875787629 313145492503636453420361)
                    ·
                      rfl

theorem cell22_914773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 5, 3].length) (baseStart_914773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_914773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_914773 prefixEnd_914773 := by exact prefixLift 914773
  have htrace : WordTrace (prefixWord ++ tailWord_914773) baseStart_914773 baseEnd_914773 := by
    simpa [prefixWord, tailWord_914773, baseEnd_914773] using wordTrace_append hprefix tailTrace_914773
  have hstable : (prefixWord ++ tailWord_914773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914773).length < 2 ^ (prefixWord ++ tailWord_914773).sum := by decide
  have hdescent : baseEnd_914773 < baseStart_914773 := by decide
  rcases family_descends (prefixWord ++ tailWord_914773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914801 : List Nat := [1, 2, 2, 2, 1, 2, 3, 2, 2, 5]
def baseStart_914801 : Nat := 118140960795 + 914801 * 2 ^ 59
def prefixEnd_914801 : Nat := 4983230072969 + 3 ^ 40 * 914801 * 2
def baseEnd_914801 : Nat := 313155077475853713720275

theorem tailTrace_914801 : CollatzResearch.WordTrace tailWord_914801 prefixEnd_914801 313155077475853713720275 := by
  unfold tailWord_914801
  simp only [CollatzResearch.WordTrace]
  refine ⟨33365533558839687417360257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22243689039226458278240171 33365533558839687417360257)
  ·
    refine ⟨25024150169129765563020193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33365533558839687417360257 25024150169129765563020193)
    ·
      refine ⟨18768112626847324172265145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25024150169129765563020193 18768112626847324172265145)
      ·
        refine ⟨14076084470135493129198859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18768112626847324172265145 14076084470135493129198859)
        ·
          refine ⟨21114126705203239693798289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14076084470135493129198859 21114126705203239693798289)
          ·
            refine ⟨15835595028902429770348717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21114126705203239693798289 15835595028902429770348717)
            ·
              refine ⟨5938348135838411163880769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15835595028902429770348717 5938348135838411163880769)
              ·
                refine ⟨4453761101878808372910577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5938348135838411163880769 4453761101878808372910577)
                ·
                  refine ⟨3340320826409106279682933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4453761101878808372910577 3340320826409106279682933)
                  ·
                    refine ⟨313155077475853713720275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3340320826409106279682933 313155077475853713720275)
                    ·
                      rfl

theorem cell22_914801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2, 5].length) (baseStart_914801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_914801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_914801 prefixEnd_914801 := by exact prefixLift 914801
  have htrace : WordTrace (prefixWord ++ tailWord_914801) baseStart_914801 baseEnd_914801 := by
    simpa [prefixWord, tailWord_914801, baseEnd_914801] using wordTrace_append hprefix tailTrace_914801
  have hstable : (prefixWord ++ tailWord_914801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914801).length < 2 ^ (prefixWord ++ tailWord_914801).sum := by decide
  have hdescent : baseEnd_914801 < baseStart_914801 := by decide
  rcases family_descends (prefixWord ++ tailWord_914801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914816 : List Nat := [2, 1, 1, 2, 1, 2, 1, 3, 5, 4]
def baseStart_914816 : Nat := 118140960795 + 914816 * 2 ^ 59
def prefixEnd_914816 : Nat := 4983230072969 + 3 ^ 40 * 914816 * 2
def baseEnd_914816 : Nat := 313160212282398674595229

theorem tailTrace_914816 : CollatzResearch.WordTrace tailWord_914816 prefixEnd_914816 313160212282398674595229 := by
  unfold tailWord_914816
  simp only [CollatzResearch.WordTrace]
  refine ⟨16683040326892672489578151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22244053769190229986104201 16683040326892672489578151)
  ·
    refine ⟨25024560490339008734367227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16683040326892672489578151 25024560490339008734367227)
    ·
      refine ⟨37536840735508513101550841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25024560490339008734367227 37536840735508513101550841)
      ·
        refine ⟨28152630551631384826163131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37536840735508513101550841 28152630551631384826163131)
        ·
          refine ⟨42228945827447077239244697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28152630551631384826163131 42228945827447077239244697)
          ·
            refine ⟨31671709370585307929433523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42228945827447077239244697 31671709370585307929433523)
            ·
              refine ⟨47507564055877961894150285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31671709370585307929433523 47507564055877961894150285)
              ·
                refine ⟨17815336520954235710306357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47507564055877961894150285 17815336520954235710306357)
                ·
                  refine ⟨1670187798839459597841221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17815336520954235710306357 1670187798839459597841221)
                  ·
                    refine ⟨313160212282398674595229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1670187798839459597841221 313160212282398674595229)
                    ·
                      rfl

theorem cell22_914816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 5, 4].length) (baseStart_914816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_914816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_914816 prefixEnd_914816 := by exact prefixLift 914816
  have htrace : WordTrace (prefixWord ++ tailWord_914816) baseStart_914816 baseEnd_914816 := by
    simpa [prefixWord, tailWord_914816, baseEnd_914816] using wordTrace_append hprefix tailTrace_914816
  have hstable : (prefixWord ++ tailWord_914816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914816).length < 2 ^ (prefixWord ++ tailWord_914816).sum := by decide
  have hdescent : baseEnd_914816 < baseStart_914816 := by decide
  rcases family_descends (prefixWord ++ tailWord_914816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914820 : List Nat := [2, 3, 2, 1, 1, 4, 3, 1, 5]
def baseStart_914820 : Nat := 118140960795 + 914820 * 2 ^ 59
def prefixEnd_914820 : Nat := 4983230072969 + 3 ^ 40 * 914820 * 2
def baseEnd_914820 : Nat := 104387193854714665831739

theorem tailTrace_914820 : CollatzResearch.WordTrace tailWord_914820 prefixEnd_914820 104387193854714665831739 := by
  unfold tailWord_914820
  simp only [CollatzResearch.WordTrace]
  refine ⟨16683113272885426831150957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22244151030513902441534609 16683113272885426831150957)
  ·
    refine ⟨6256167477332035061681609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16683113272885426831150957 6256167477332035061681609)
    ·
      refine ⟨4692125607999026296261207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6256167477332035061681609 4692125607999026296261207)
      ·
        refine ⟨7038188411998539444391811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4692125607999026296261207 7038188411998539444391811)
        ·
          refine ⟨10557282617997809166587717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7038188411998539444391811 10557282617997809166587717)
          ·
            refine ⟨1979490490874589218735197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10557282617997809166587717 1979490490874589218735197)
            ·
              refine ⟨742308934077970957025699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1979490490874589218735197 742308934077970957025699)
              ·
                refine ⟨1113463401116956435538549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 742308934077970957025699 1113463401116956435538549)
                ·
                  refine ⟨104387193854714665831739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1113463401116956435538549 104387193854714665831739)
                  ·
                    rfl

theorem cell22_914820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 1, 5].length) (baseStart_914820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_914820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_914820 prefixEnd_914820 := by exact prefixLift 914820
  have htrace : WordTrace (prefixWord ++ tailWord_914820) baseStart_914820 baseEnd_914820 := by
    simpa [prefixWord, tailWord_914820, baseEnd_914820] using wordTrace_append hprefix tailTrace_914820
  have hstable : (prefixWord ++ tailWord_914820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914820).length < 2 ^ (prefixWord ++ tailWord_914820).sum := by decide
  have hdescent : baseEnd_914820 < baseStart_914820 := by decide
  rcases family_descends (prefixWord ++ tailWord_914820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914850 : List Nat := [3, 3, 1, 2, 1, 2, 2, 3, 1, 4]
def baseStart_914850 : Nat := 118140960795 + 914850 * 2 ^ 59
def prefixEnd_914850 : Nat := 4983230072969 + 3 ^ 40 * 914850 * 2
def baseEnd_914850 : Nat := 313171851177233919245125

theorem tailTrace_914850 : CollatzResearch.WordTrace tailWord_914850 prefixEnd_914850 313171851177233919245125 := by
  unfold tailWord_914850
  simp only [CollatzResearch.WordTrace]
  refine ⟨8341830183915542196473501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22244880490441445857262669 8341830183915542196473501)
  ·
    refine ⟨3128186318968328323677563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8341830183915542196473501 3128186318968328323677563)
    ·
      refine ⟨4692279478452492485516345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3128186318968328323677563 4692279478452492485516345)
      ·
        refine ⟨3519209608839369364137259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4692279478452492485516345 3519209608839369364137259)
        ·
          refine ⟨5278814413259054046205889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3519209608839369364137259 5278814413259054046205889)
          ·
            refine ⟨3959110809944290534654417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5278814413259054046205889 3959110809944290534654417)
            ·
              refine ⟨2969333107458217900990813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3959110809944290534654417 2969333107458217900990813)
              ·
                refine ⟨1113499915296831712871555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2969333107458217900990813 1113499915296831712871555)
                ·
                  refine ⟨1670249872945247569307333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1113499915296831712871555 1670249872945247569307333)
                  ·
                    refine ⟨313171851177233919245125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1670249872945247569307333 313171851177233919245125)
                    ·
                      rfl

theorem cell22_914850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_914850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_914850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_914850 prefixEnd_914850 := by exact prefixLift 914850
  have htrace : WordTrace (prefixWord ++ tailWord_914850) baseStart_914850 baseEnd_914850 := by
    simpa [prefixWord, tailWord_914850, baseEnd_914850] using wordTrace_append hprefix tailTrace_914850
  have hstable : (prefixWord ++ tailWord_914850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914850).length < 2 ^ (prefixWord ++ tailWord_914850).sum := by decide
  have hdescent : baseEnd_914850 < baseStart_914850 := by decide
  rcases family_descends (prefixWord ++ tailWord_914850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914878 : List Nat := [4, 2, 1, 1, 1, 1, 1, 1, 6, 4]
def baseStart_914878 : Nat := 118140960795 + 914878 * 2 ^ 59
def prefixEnd_914878 : Nat := 4983230072969 + 3 ^ 40 * 914878 * 2
def baseEnd_914878 : Nat := 313181436149451179545039

theorem tailTrace_914878 : CollatzResearch.WordTrace tailWord_914878 prefixEnd_914878 313181436149451179545039 := by
  unfold tailWord_914878
  simp only [CollatzResearch.WordTrace]
  refine ⟨4171042747445091195989161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22245561319707153045275525 4171042747445091195989161)
  ·
    refine ⟨3128282060583818396991871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4171042747445091195989161 3128282060583818396991871)
    ·
      refine ⟨4692423090875727595487807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3128282060583818396991871 4692423090875727595487807)
      ·
        refine ⟨7038634636313591393231711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4692423090875727595487807 7038634636313591393231711)
        ·
          refine ⟨10557951954470387089847567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7038634636313591393231711 10557951954470387089847567)
          ·
            refine ⟨15836927931705580634771351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10557951954470387089847567 15836927931705580634771351)
            ·
              refine ⟨23755391897558370952157027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15836927931705580634771351 23755391897558370952157027)
              ·
                refine ⟨35633087846337556428235541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23755391897558370952157027 35633087846337556428235541)
                ·
                  refine ⟨1670300992797072957573541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 35633087846337556428235541 1670300992797072957573541)
                  ·
                    refine ⟨313181436149451179545039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1670300992797072957573541 313181436149451179545039)
                    ·
                      rfl

theorem cell22_914878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_914878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_914878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_914878 prefixEnd_914878 := by exact prefixLift 914878
  have htrace : WordTrace (prefixWord ++ tailWord_914878) baseStart_914878 baseEnd_914878 := by
    simpa [prefixWord, tailWord_914878, baseEnd_914878] using wordTrace_append hprefix tailTrace_914878
  have hstable : (prefixWord ++ tailWord_914878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914878).length < 2 ^ (prefixWord ++ tailWord_914878).sum := by decide
  have hdescent : baseEnd_914878 < baseStart_914878 := by decide
  rcases family_descends (prefixWord ++ tailWord_914878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914891 : List Nat := [1, 1, 1, 1, 3, 3, 2, 1, 2, 7]
def baseStart_914891 : Nat := 118140960795 + 914891 * 2 ^ 59
def prefixEnd_914891 : Nat := 4983230072969 + 3 ^ 40 * 914891 * 2
def baseEnd_914891 : Nat := 313185886315123478969999

theorem tailTrace_914891 : CollatzResearch.WordTrace tailWord_914891 prefixEnd_914891 313185886315123478969999 := by
  unfold tailWord_914891
  simp only [CollatzResearch.WordTrace]
  refine ⟨33368816128513632788136527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22245877419009088525424351 33368816128513632788136527)
  ·
    refine ⟨50053224192770449182204791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33368816128513632788136527 50053224192770449182204791)
    ·
      refine ⟨75079836289155673773307187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50053224192770449182204791 75079836289155673773307187)
      ·
        refine ⟨112619754433733510659960781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75079836289155673773307187 112619754433733510659960781)
        ·
          refine ⟨42232407912650066497485293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112619754433733510659960781 42232407912650066497485293)
          ·
            refine ⟨15837152967243774936556985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42232407912650066497485293 15837152967243774936556985)
            ·
              refine ⟨11877864725432831202417739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15837152967243774936556985 11877864725432831202417739)
              ·
                refine ⟨17816797088149246803626609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11877864725432831202417739 17816797088149246803626609)
                ·
                  refine ⟨13362597816111935102719957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17816797088149246803626609 13362597816111935102719957)
                  ·
                    refine ⟨313185886315123478969999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13362597816111935102719957 313185886315123478969999)
                    ·
                      rfl

theorem cell22_914891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 7].length) (baseStart_914891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_914891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_914891 prefixEnd_914891 := by exact prefixLift 914891
  have htrace : WordTrace (prefixWord ++ tailWord_914891) baseStart_914891 baseEnd_914891 := by
    simpa [prefixWord, tailWord_914891, baseEnd_914891] using wordTrace_append hprefix tailTrace_914891
  have hstable : (prefixWord ++ tailWord_914891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914891).length < 2 ^ (prefixWord ++ tailWord_914891).sum := by decide
  have hdescent : baseEnd_914891 < baseStart_914891 := by decide
  rcases family_descends (prefixWord ++ tailWord_914891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914921 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 11]
def baseStart_914921 : Nat := 118140960795 + 914921 * 2 ^ 59
def prefixEnd_914921 : Nat := 4983230072969 + 3 ^ 40 * 914921 * 2
def baseEnd_914921 : Nat := 104398718642737800239969

theorem tailTrace_914921 : CollatzResearch.WordTrace tailWord_914921 prefixEnd_914921 104398718642737800239969 := by
  unfold tailWord_914921
  simp only [CollatzResearch.WordTrace]
  refine ⟨33369910318404947911728617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22246606878936631941152411 33369910318404947911728617)
  ·
    refine ⟨25027432738803710933796463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33369910318404947911728617 25027432738803710933796463)
    ·
      refine ⟨37541149108205566400694695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25027432738803710933796463 37541149108205566400694695)
      ·
        refine ⟨56311723662308349601042043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37541149108205566400694695 56311723662308349601042043)
        ·
          refine ⟨84467585493462524401563065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56311723662308349601042043 84467585493462524401563065)
          ·
            refine ⟨63350689120096893301172299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84467585493462524401563065 63350689120096893301172299)
            ·
              refine ⟨95026033680145339951758449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63350689120096893301172299 95026033680145339951758449)
              ·
                refine ⟨71269525260109004963818837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95026033680145339951758449 71269525260109004963818837)
                ·
                  refine ⟨104398718642737800239969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 71269525260109004963818837 104398718642737800239969)
                  ·
                    rfl

theorem cell22_914921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 11].length) (baseStart_914921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_914921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_914921 prefixEnd_914921 := by exact prefixLift 914921
  have htrace : WordTrace (prefixWord ++ tailWord_914921) baseStart_914921 baseEnd_914921 := by
    simpa [prefixWord, tailWord_914921, baseEnd_914921] using wordTrace_append hprefix tailTrace_914921
  have hstable : (prefixWord ++ tailWord_914921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914921).length < 2 ^ (prefixWord ++ tailWord_914921).sum := by decide
  have hdescent : baseEnd_914921 < baseStart_914921 := by decide
  rcases family_descends (prefixWord ++ tailWord_914921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_914938 : List Nat := [3, 1, 1, 1, 1, 2, 3, 5, 5]
def baseStart_914938 : Nat := 118140960795 + 914938 * 2 ^ 59
def prefixEnd_914938 : Nat := 4983230072969 + 3 ^ 40 * 914938 * 2
def baseEnd_914938 : Nat := 104400658458543674348285

theorem tailTrace_914938 : CollatzResearch.WordTrace tailWord_914938 prefixEnd_914938 104400658458543674348285 := by
  unfold tailWord_914938
  simp only [CollatzResearch.WordTrace]
  refine ⟨8342632589835839953774367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22247020239562239876731645 8342632589835839953774367)
  ·
    refine ⟨12513948884753759930661551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8342632589835839953774367 12513948884753759930661551)
    ·
      refine ⟨18770923327130639895992327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12513948884753759930661551 18770923327130639895992327)
      ·
        refine ⟨28156384990695959843988491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18770923327130639895992327 28156384990695959843988491)
        ·
          refine ⟨42234577486043939765982737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28156384990695959843988491 42234577486043939765982737)
          ·
            refine ⟨31675933114532954824487053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42234577486043939765982737 31675933114532954824487053)
            ·
              refine ⟨11878474917949858059182645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31675933114532954824487053 11878474917949858059182645)
              ·
                refine ⟨1113607023557799193048373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11878474917949858059182645 1113607023557799193048373)
                ·
                  refine ⟨104400658458543674348285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1113607023557799193048373 104400658458543674348285)
                  ·
                    rfl

theorem cell22_914938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 5, 5].length) (baseStart_914938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_914938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_914938 prefixEnd_914938 := by exact prefixLift 914938
  have htrace : WordTrace (prefixWord ++ tailWord_914938) baseStart_914938 baseEnd_914938 := by
    simpa [prefixWord, tailWord_914938, baseEnd_914938] using wordTrace_append hprefix tailTrace_914938
  have hstable : (prefixWord ++ tailWord_914938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_914938).length < 2 ^ (prefixWord ++ tailWord_914938).sum := by decide
  have hdescent : baseEnd_914938 < baseStart_914938 := by decide
  rcases family_descends (prefixWord ++ tailWord_914938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915013 : List Nat := [1, 3, 1, 1, 1, 4, 1, 3, 1, 6]
def baseStart_915013 : Nat := 118140960795 + 915013 * 2 ^ 59
def prefixEnd_915013 : Nat := 4983230072969 + 3 ^ 40 * 915013 * 2
def baseEnd_915013 : Nat := 313227649408355827419625

theorem tailTrace_915013 : CollatzResearch.WordTrace tailWord_915013 prefixEnd_915013 313227649408355827419625 := by
  unfold tailWord_915013
  simp only [CollatzResearch.WordTrace]
  refine ⟨33373265834071647624077693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22248843889381098416051795 33373265834071647624077693)
  ·
    refine ⟨12514974687776867859029135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33373265834071647624077693 12514974687776867859029135)
    ·
      refine ⟨18772462031665301788543703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12514974687776867859029135 18772462031665301788543703)
      ·
        refine ⟨28158693047497952682815555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18772462031665301788543703 28158693047497952682815555)
        ·
          refine ⟨42238039571246929024223333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28158693047497952682815555 42238039571246929024223333)
          ·
            refine ⟨7919632419608799192041875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42238039571246929024223333 7919632419608799192041875)
            ·
              refine ⟨11879448629413198788062813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7919632419608799192041875 11879448629413198788062813)
              ·
                refine ⟨4454793236029949545523555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11879448629413198788062813 4454793236029949545523555)
                ·
                  refine ⟨6682189854044924318285333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4454793236029949545523555 6682189854044924318285333)
                  ·
                    refine ⟨313227649408355827419625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6682189854044924318285333 313227649408355827419625)
                    ·
                      rfl

theorem cell22_915013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 6].length) (baseStart_915013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_915013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_915013 prefixEnd_915013 := by exact prefixLift 915013
  have htrace : WordTrace (prefixWord ++ tailWord_915013) baseStart_915013 baseEnd_915013 := by
    simpa [prefixWord, tailWord_915013, baseEnd_915013] using wordTrace_append hprefix tailTrace_915013
  have hstable : (prefixWord ++ tailWord_915013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915013).length < 2 ^ (prefixWord ++ tailWord_915013).sum := by decide
  have hdescent : baseEnd_915013 < baseStart_915013 := by decide
  rcases family_descends (prefixWord ++ tailWord_915013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915045 : List Nat := [1, 3, 1, 3, 3, 2, 2, 7]
def baseStart_915045 : Nat := 118140960795 + 915045 * 2 ^ 59
def prefixEnd_915045 : Nat := 4983230072969 + 3 ^ 40 * 915045 * 2
def baseEnd_915045 : Nat := 34804289295813156735503

theorem tailTrace_915045 : CollatzResearch.WordTrace tailWord_915045 prefixEnd_915045 34804289295813156735503 := by
  unfold tailWord_915045
  simp only [CollatzResearch.WordTrace]
  refine ⟨33374432969955717089242589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22249621979970478059495059 33374432969955717089242589)
  ·
    refine ⟨12515412363733393908465971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33374432969955717089242589 12515412363733393908465971)
    ·
      refine ⟨18773118545600090862698957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12515412363733393908465971 18773118545600090862698957)
      ·
        refine ⟨7039919454600034073512109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18773118545600090862698957 7039919454600034073512109)
        ·
          refine ⟨2639969795475012777567041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7039919454600034073512109 2639969795475012777567041)
          ·
            refine ⟨1979977346606259583175281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2639969795475012777567041 1979977346606259583175281)
            ·
              refine ⟨1484983009954694687381461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1979977346606259583175281 1484983009954694687381461)
              ·
                refine ⟨34804289295813156735503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1484983009954694687381461 34804289295813156735503)
                ·
                  rfl

theorem cell22_915045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 7].length) (baseStart_915045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_915045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_915045 prefixEnd_915045 := by exact prefixLift 915045
  have htrace : WordTrace (prefixWord ++ tailWord_915045) baseStart_915045 baseEnd_915045 := by
    simpa [prefixWord, tailWord_915045, baseEnd_915045] using wordTrace_append hprefix tailTrace_915045
  have hstable : (prefixWord ++ tailWord_915045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915045).length < 2 ^ (prefixWord ++ tailWord_915045).sum := by decide
  have hdescent : baseEnd_915045 < baseStart_915045 := by decide
  rcases family_descends (prefixWord ++ tailWord_915045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915088 : List Nat := [2, 1, 1, 1, 1, 1, 3, 2, 3, 7]
def baseStart_915088 : Nat := 118140960795 + 915088 * 2 ^ 59
def prefixEnd_915088 : Nat := 4983230072969 + 3 ^ 40 * 915088 * 2
def baseEnd_915088 : Nat := 313253323441080631794395

theorem tailTrace_915088 : CollatzResearch.WordTrace tailWord_915088 prefixEnd_915088 313253323441080631794395 := by
  unfold tailWord_915088
  simp only [CollatzResearch.WordTrace]
  refine ⟨16688000654399967716528959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22250667539199956955371945 16688000654399967716528959)
  ·
    refine ⟨25032000981599951574793439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16688000654399967716528959 25032000981599951574793439)
    ·
      refine ⟨37548001472399927362190159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25032000981599951574793439 37548001472399927362190159)
      ·
        refine ⟨56322002208599891043285239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37548001472399927362190159 56322002208599891043285239)
        ·
          refine ⟨84483003312899836564927859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56322002208599891043285239 84483003312899836564927859)
          ·
            refine ⟨126724504969349754847391789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84483003312899836564927859 126724504969349754847391789)
            ·
              refine ⟨47521689363506158067771921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126724504969349754847391789 47521689363506158067771921)
              ·
                refine ⟨35641267022629618550828941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47521689363506158067771921 35641267022629618550828941)
                ·
                  refine ⟨13365475133486106956560853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35641267022629618550828941 13365475133486106956560853)
                  ·
                    refine ⟨313253323441080631794395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13365475133486106956560853 313253323441080631794395)
                    ·
                      rfl

theorem cell22_915088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 3, 7].length) (baseStart_915088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_915088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_915088 prefixEnd_915088 := by exact prefixLift 915088
  have htrace : WordTrace (prefixWord ++ tailWord_915088) baseStart_915088 baseEnd_915088 := by
    simpa [prefixWord, tailWord_915088, baseEnd_915088] using wordTrace_append hprefix tailTrace_915088
  have hstable : (prefixWord ++ tailWord_915088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915088).length < 2 ^ (prefixWord ++ tailWord_915088).sum := by decide
  have hdescent : baseEnd_915088 < baseStart_915088 := by decide
  rcases family_descends (prefixWord ++ tailWord_915088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915105 : List Nat := [1, 2, 3, 3, 2, 1, 1, 1, 1, 7]
def baseStart_915105 : Nat := 118140960795 + 915105 * 2 ^ 59
def prefixEnd_915105 : Nat := 4983230072969 + 3 ^ 40 * 915105 * 2
def baseEnd_915105 : Nat := 313259142888498254119343

theorem tailTrace_915105 : CollatzResearch.WordTrace tailWord_915105 prefixEnd_915105 313259142888498254119343 := by
  unfold tailWord_915105
  simp only [CollatzResearch.WordTrace]
  refine ⟨33376621349738347336426769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22251080899825564890951179 33376621349738347336426769)
  ·
    refine ⟨25032466012303760502320077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33376621349738347336426769 25032466012303760502320077)
    ·
      refine ⟨9387174754613910188370029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25032466012303760502320077 9387174754613910188370029)
      ·
        refine ⟨3520190532980216320638761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9387174754613910188370029 3520190532980216320638761)
        ·
          refine ⟨2640142899735162240479071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3520190532980216320638761 2640142899735162240479071)
          ·
            refine ⟨3960214349602743360718607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2640142899735162240479071 3960214349602743360718607)
            ·
              refine ⟨5940321524404115041077911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3960214349602743360718607 5940321524404115041077911)
              ·
                refine ⟨8910482286606172561616867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5940321524404115041077911 8910482286606172561616867)
                ·
                  refine ⟨13365723429909258842425301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8910482286606172561616867 13365723429909258842425301)
                  ·
                    refine ⟨313259142888498254119343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13365723429909258842425301 313259142888498254119343)
                    ·
                      rfl

theorem cell22_915105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_915105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_915105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_915105 prefixEnd_915105 := by exact prefixLift 915105
  have htrace : WordTrace (prefixWord ++ tailWord_915105) baseStart_915105 baseEnd_915105 := by
    simpa [prefixWord, tailWord_915105, baseEnd_915105] using wordTrace_append hprefix tailTrace_915105
  have hstable : (prefixWord ++ tailWord_915105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915105).length < 2 ^ (prefixWord ++ tailWord_915105).sum := by decide
  have hdescent : baseEnd_915105 < baseStart_915105 := by decide
  rcases family_descends (prefixWord ++ tailWord_915105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915120 : List Nat := [2, 1, 1, 1, 2, 1, 6, 1, 3, 4]
def baseStart_915120 : Nat := 118140960795 + 915120 * 2 ^ 59
def prefixEnd_915120 : Nat := 4983230072969 + 3 ^ 40 * 915120 * 2
def baseEnd_915120 : Nat := 313264277695043214994297

theorem tailTrace_915120 : CollatzResearch.WordTrace tailWord_915120 prefixEnd_915120 313264277695043214994297 := by
  unfold tailWord_915120
  simp only [CollatzResearch.WordTrace]
  refine ⟨16688584222342002449111407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22251445629789336598815209 16688584222342002449111407)
  ·
    refine ⟨25032876333513003673667111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16688584222342002449111407 25032876333513003673667111)
    ·
      refine ⟨37549314500269505510500667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25032876333513003673667111 37549314500269505510500667)
      ·
        refine ⟨56323971750404258265751001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37549314500269505510500667 56323971750404258265751001)
        ·
          refine ⟨42242978812803193699313251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56323971750404258265751001 42242978812803193699313251)
          ·
            refine ⟨63364468219204790548969877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42242978812803193699313251 63364468219204790548969877)
            ·
              refine ⟨2970209447775224556982963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 63364468219204790548969877 2970209447775224556982963)
              ·
                refine ⟨4455314171662836835474445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2970209447775224556982963 4455314171662836835474445)
                ·
                  refine ⟨1670742814373563813302917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4455314171662836835474445 1670742814373563813302917)
                  ·
                    refine ⟨313264277695043214994297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1670742814373563813302917 313264277695043214994297)
                    ·
                      rfl

theorem cell22_915120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 3, 4].length) (baseStart_915120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_915120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_915120 prefixEnd_915120 := by exact prefixLift 915120
  have htrace : WordTrace (prefixWord ++ tailWord_915120) baseStart_915120 baseEnd_915120 := by
    simpa [prefixWord, tailWord_915120, baseEnd_915120] using wordTrace_append hprefix tailTrace_915120
  have hstable : (prefixWord ++ tailWord_915120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915120).length < 2 ^ (prefixWord ++ tailWord_915120).sum := by decide
  have hdescent : baseEnd_915120 < baseStart_915120 := by decide
  rcases family_descends (prefixWord ++ tailWord_915120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915158 : List Nat := [5, 2, 1, 3, 1, 1, 3, 1, 5]
def baseStart_915158 : Nat := 118140960795 + 915158 * 2 ^ 59
def prefixEnd_915158 : Nat := 4983230072969 + 3 ^ 40 * 915158 * 2
def baseEnd_915158 : Nat := 104425761957207927514727

theorem tailTrace_915158 : CollatzResearch.WordTrace tailWord_915158 prefixEnd_915158 104425761957207927514727 := by
  unfold tailWord_915158
  simp only [CollatzResearch.WordTrace]
  refine ⟨2086159651159146086756633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22252369612364224925404085 2086159651159146086756633)
  ·
    refine ⟨1564619738369359565067475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2086159651159146086756633 1564619738369359565067475)
    ·
      refine ⟨2346929607554039347601213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1564619738369359565067475 2346929607554039347601213)
      ·
        refine ⟨880098602832764755350455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2346929607554039347601213 880098602832764755350455)
        ·
          refine ⟨1320147904249147133025683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 880098602832764755350455 1320147904249147133025683)
          ·
            refine ⟨1980221856373720699538525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1320147904249147133025683 1980221856373720699538525)
            ·
              refine ⟨742583196140145262326947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1980221856373720699538525 742583196140145262326947)
              ·
                refine ⟨1113874794210217893490421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 742583196140145262326947 1113874794210217893490421)
                ·
                  refine ⟨104425761957207927514727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1113874794210217893490421 104425761957207927514727)
                  ·
                    rfl

theorem cell22_915158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_915158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_915158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_915158 prefixEnd_915158 := by exact prefixLift 915158
  have htrace : WordTrace (prefixWord ++ tailWord_915158) baseStart_915158 baseEnd_915158 := by
    simpa [prefixWord, tailWord_915158, baseEnd_915158] using wordTrace_append hprefix tailTrace_915158
  have hstable : (prefixWord ++ tailWord_915158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915158).length < 2 ^ (prefixWord ++ tailWord_915158).sum := by decide
  have hdescent : baseEnd_915158 < baseStart_915158 := by decide
  rcases family_descends (prefixWord ++ tailWord_915158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915182 : List Nat := [4, 1, 2, 1, 1, 2, 2, 3, 2, 4]
def baseStart_915182 : Nat := 118140960795 + 915182 * 2 ^ 59
def prefixEnd_915182 : Nat := 4983230072969 + 3 ^ 40 * 915182 * 2
def baseEnd_915182 : Nat := 313285501562095719944107

theorem tailTrace_915182 : CollatzResearch.WordTrace tailWord_915182 prefixEnd_915182 313285501562095719944107 := by
  unfold tailWord_915182
  simp only [CollatzResearch.WordTrace]
  refine ⟨4172428721307423685872475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22252953180306259657986533 4172428721307423685872475)
  ·
    refine ⟨6258643081961135528808713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4172428721307423685872475 6258643081961135528808713)
    ·
      refine ⟨4693982311470851646606535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6258643081961135528808713 4693982311470851646606535)
      ·
        refine ⟨7040973467206277469909803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4693982311470851646606535 7040973467206277469909803)
        ·
          refine ⟨10561460200809416204864705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7040973467206277469909803 10561460200809416204864705)
          ·
            refine ⟨7921095150607062153648529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10561460200809416204864705 7921095150607062153648529)
            ·
              refine ⟨5940821362955296615236397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7921095150607062153648529 5940821362955296615236397)
              ·
                refine ⟨2227808011108236230713649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5940821362955296615236397 2227808011108236230713649)
                ·
                  refine ⟨1670856008331177173035237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2227808011108236230713649 1670856008331177173035237)
                  ·
                    refine ⟨313285501562095719944107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1670856008331177173035237 313285501562095719944107)
                    ·
                      rfl

theorem cell22_915182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_915182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_915182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_915182 prefixEnd_915182 := by exact prefixLift 915182
  have htrace : WordTrace (prefixWord ++ tailWord_915182) baseStart_915182 baseEnd_915182 := by
    simpa [prefixWord, tailWord_915182, baseEnd_915182] using wordTrace_append hprefix tailTrace_915182
  have hstable : (prefixWord ++ tailWord_915182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915182).length < 2 ^ (prefixWord ++ tailWord_915182).sum := by decide
  have hdescent : baseEnd_915182 < baseStart_915182 := by decide
  rcases family_descends (prefixWord ++ tailWord_915182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915218 : List Nat := [3, 2, 4, 1, 1, 1, 4, 1, 2, 3]
def baseStart_915218 : Nat := 118140960795 + 915218 * 2 ^ 59
def prefixEnd_915218 : Nat := 4983230072969 + 3 ^ 40 * 915218 * 2
def baseEnd_915218 : Nat := 313297825097803626043997

theorem tailTrace_915218 : CollatzResearch.WordTrace tailWord_915218 prefixEnd_915218 313297825097803626043997 := by
  unfold tailWord_915218
  simp only [CollatzResearch.WordTrace]
  refine ⟨8345185699582241908822577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22253828532219311756860205 8345185699582241908822577)
  ·
    refine ⟨6258889274686681431616933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8345185699582241908822577 6258889274686681431616933)
    ·
      refine ⟨1173541739003752768428175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6258889274686681431616933 1173541739003752768428175)
      ·
        refine ⟨1760312608505629152642263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1173541739003752768428175 1760312608505629152642263)
        ·
          refine ⟨2640468912758443728963395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1760312608505629152642263 2640468912758443728963395)
          ·
            refine ⟨3960703369137665593445093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2640468912758443728963395 3960703369137665593445093)
            ·
              refine ⟨742631881713312298770955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3960703369137665593445093 742631881713312298770955)
              ·
                refine ⟨1113947822569968448156433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 742631881713312298770955 1113947822569968448156433)
                ·
                  refine ⟨835460866927476336117325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1113947822569968448156433 835460866927476336117325)
                  ·
                    refine ⟨313297825097803626043997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 835460866927476336117325 313297825097803626043997)
                    ·
                      rfl

theorem cell22_915218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_915218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_915218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_915218 prefixEnd_915218 := by exact prefixLift 915218
  have htrace : WordTrace (prefixWord ++ tailWord_915218) baseStart_915218 baseEnd_915218 := by
    simpa [prefixWord, tailWord_915218, baseEnd_915218] using wordTrace_append hprefix tailTrace_915218
  have hstable : (prefixWord ++ tailWord_915218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915218).length < 2 ^ (prefixWord ++ tailWord_915218).sum := by decide
  have hdescent : baseEnd_915218 < baseStart_915218 := by decide
  rcases family_descends (prefixWord ++ tailWord_915218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915272 : List Nat := [2, 1, 3, 1, 1, 4, 1, 2, 3, 4]
def baseStart_915272 : Nat := 118140960795 + 915272 * 2 ^ 59
def prefixEnd_915272 : Nat := 4983230072969 + 3 ^ 40 * 915272 * 2
def baseEnd_915272 : Nat := 313316310401365485193831

theorem tailTrace_915272 : CollatzResearch.WordTrace tailWord_915272 prefixEnd_915272 313316310401365485193831 := by
  unfold tailWord_915272
  simp only [CollatzResearch.WordTrace]
  refine ⟨16691356170066667428878035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22255141560088889905170713 16691356170066667428878035)
  ·
    refine ⟨25037034255100001143317053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16691356170066667428878035 25037034255100001143317053)
    ·
      refine ⟨9388887845662500428743895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25037034255100001143317053 9388887845662500428743895)
      ·
        refine ⟨14083331768493750643115843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9388887845662500428743895 14083331768493750643115843)
        ·
          refine ⟨21124997652740625964673765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14083331768493750643115843 21124997652740625964673765)
          ·
            refine ⟨3960937059888867368376331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21124997652740625964673765 3960937059888867368376331)
            ·
              refine ⟨5941405589833301052564497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3960937059888867368376331 5941405589833301052564497)
              ·
                refine ⟨4456054192374975789423373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5941405589833301052564497 4456054192374975789423373)
                ·
                  refine ⟨1671020322140615921033765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4456054192374975789423373 1671020322140615921033765)
                  ·
                    refine ⟨313316310401365485193831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1671020322140615921033765 313316310401365485193831)
                    ·
                      rfl

theorem cell22_915272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_915272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_915272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_915272 prefixEnd_915272 := by exact prefixLift 915272
  have htrace : WordTrace (prefixWord ++ tailWord_915272) baseStart_915272 baseEnd_915272 := by
    simpa [prefixWord, tailWord_915272, baseEnd_915272] using wordTrace_append hprefix tailTrace_915272
  have hstable : (prefixWord ++ tailWord_915272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915272).length < 2 ^ (prefixWord ++ tailWord_915272).sum := by decide
  have hdescent : baseEnd_915272 < baseStart_915272 := by decide
  rcases family_descends (prefixWord ++ tailWord_915272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915336 : List Nat := [2, 1, 3, 3, 3, 2, 1, 1, 1, 5]
def baseStart_915336 : Nat := 118140960795 + 915336 * 2 ^ 59
def prefixEnd_915336 : Nat := 4983230072969 + 3 ^ 40 * 915336 * 2
def baseEnd_915336 : Nat := 313338218909290651593635

theorem tailTrace_915336 : CollatzResearch.WordTrace tailWord_915336 prefixEnd_915336 313338218909290651593635 := by
  unfold tailWord_915336
  simp only [CollatzResearch.WordTrace]
  refine ⟨16692523305950736894042931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22256697741267649192057241 16692523305950736894042931)
  ·
    refine ⟨25038784958926105341064397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16692523305950736894042931 25038784958926105341064397)
    ·
      refine ⟨9389544359597289502899149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25038784958926105341064397 9389544359597289502899149)
      ·
        refine ⟨3521079134848983563587181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9389544359597289502899149 3521079134848983563587181)
        ·
          refine ⟨1320404675568368836345193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3521079134848983563587181 1320404675568368836345193)
          ·
            refine ⟨990303506676276627258895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1320404675568368836345193 990303506676276627258895)
            ·
              refine ⟨1485455260014414940888343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 990303506676276627258895 1485455260014414940888343)
              ·
                refine ⟨2228182890021622411332515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1485455260014414940888343 2228182890021622411332515)
                ·
                  refine ⟨3342274335032433616998773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2228182890021622411332515 3342274335032433616998773)
                  ·
                    refine ⟨313338218909290651593635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3342274335032433616998773 313338218909290651593635)
                    ·
                      rfl

theorem cell22_915336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 1, 1, 5].length) (baseStart_915336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_915336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_915336 prefixEnd_915336 := by exact prefixLift 915336
  have htrace : WordTrace (prefixWord ++ tailWord_915336) baseStart_915336 baseEnd_915336 := by
    simpa [prefixWord, tailWord_915336, baseEnd_915336] using wordTrace_append hprefix tailTrace_915336
  have hstable : (prefixWord ++ tailWord_915336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915336).length < 2 ^ (prefixWord ++ tailWord_915336).sum := by decide
  have hdescent : baseEnd_915336 < baseStart_915336 := by decide
  rcases family_descends (prefixWord ++ tailWord_915336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915368 : List Nat := [2, 1, 6, 2, 1, 1, 1, 2, 2, 4]
def baseStart_915368 : Nat := 118140960795 + 915368 * 2 ^ 59
def prefixEnd_915368 : Nat := 4983230072969 + 3 ^ 40 * 915368 * 2
def baseEnd_915368 : Nat := 313349173163253234793537

theorem tailTrace_915368 : CollatzResearch.WordTrace tailWord_915368 prefixEnd_915368 313349173163253234793537 := by
  unfold tailWord_915368
  simp only [CollatzResearch.WordTrace]
  refine ⟨16693106873892771626625379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22257475831857028835500505 16693106873892771626625379)
  ·
    refine ⟨25039660310839157439938069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16693106873892771626625379 25039660310839157439938069)
    ·
      refine ⟨1173734077070585504997097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 25039660310839157439938069 1173734077070585504997097)
      ·
        refine ⟨880300557802939128747823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1173734077070585504997097 880300557802939128747823)
        ·
          refine ⟨1320450836704408693121735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 880300557802939128747823 1320450836704408693121735)
          ·
            refine ⟨1980676255056613039682603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1320450836704408693121735 1980676255056613039682603)
            ·
              refine ⟨2971014382584919559523905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1980676255056613039682603 2971014382584919559523905)
              ·
                refine ⟨2228260786938689669642929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2971014382584919559523905 2228260786938689669642929)
                ·
                  refine ⟨1671195590204017252232197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2228260786938689669642929 1671195590204017252232197)
                  ·
                    refine ⟨313349173163253234793537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1671195590204017252232197 313349173163253234793537)
                    ·
                      rfl

theorem cell22_915368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_915368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_915368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_915368 prefixEnd_915368 := by exact prefixLift 915368
  have htrace : WordTrace (prefixWord ++ tailWord_915368) baseStart_915368 baseEnd_915368 := by
    simpa [prefixWord, tailWord_915368, baseEnd_915368] using wordTrace_append hprefix tailTrace_915368
  have hstable : (prefixWord ++ tailWord_915368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915368).length < 2 ^ (prefixWord ++ tailWord_915368).sum := by decide
  have hdescent : baseEnd_915368 < baseStart_915368 := by decide
  rcases family_descends (prefixWord ++ tailWord_915368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915381 : List Nat := [1, 3, 3, 2, 1, 2, 3, 1, 3, 3]
def baseStart_915381 : Nat := 118140960795 + 915381 * 2 ^ 59
def prefixEnd_915381 : Nat := 4983230072969 + 3 ^ 40 * 915381 * 2
def baseEnd_915381 : Nat := 313353623328925534218497

theorem tailTrace_915381 : CollatzResearch.WordTrace tailWord_915381 prefixEnd_915381 313353623328925534218497 := by
  unfold tailWord_915381
  simp only [CollatzResearch.WordTrace]
  refine ⟨33386687896738446473473997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22257791931158964315649331 33386687896738446473473997)
  ·
    refine ⟨12520007961276917427552749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33386687896738446473473997 12520007961276917427552749)
    ·
      refine ⟨4695002985478844035332281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12520007961276917427552749 4695002985478844035332281)
      ·
        refine ⟨3521252239109133026499211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4695002985478844035332281 3521252239109133026499211)
        ·
          refine ⟨5281878358663699539748817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3521252239109133026499211 5281878358663699539748817)
          ·
            refine ⟨3961408768997774654811613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5281878358663699539748817 3961408768997774654811613)
            ·
              refine ⟨1485528288374165495554355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3961408768997774654811613 1485528288374165495554355)
              ·
                refine ⟨2228292432561248243331533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1485528288374165495554355 2228292432561248243331533)
                ·
                  refine ⟨835609662210468091249325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2228292432561248243331533 835609662210468091249325)
                  ·
                    refine ⟨313353623328925534218497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 835609662210468091249325 313353623328925534218497)
                    ·
                      rfl

theorem cell22_915381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_915381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_915381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_915381 prefixEnd_915381 := by exact prefixLift 915381
  have htrace : WordTrace (prefixWord ++ tailWord_915381) baseStart_915381 baseEnd_915381 := by
    simpa [prefixWord, tailWord_915381, baseEnd_915381] using wordTrace_append hprefix tailTrace_915381
  have hstable : (prefixWord ++ tailWord_915381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915381).length < 2 ^ (prefixWord ++ tailWord_915381).sum := by decide
  have hdescent : baseEnd_915381 < baseStart_915381 := by decide
  rcases family_descends (prefixWord ++ tailWord_915381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915392 : List Nat := [2, 1, 1, 2, 3, 2, 2, 1, 1, 7]
def baseStart_915392 : Nat := 118140960795 + 915392 * 2 ^ 59
def prefixEnd_915392 : Nat := 4983230072969 + 3 ^ 40 * 915392 * 2
def baseEnd_915392 : Nat := 313357388853725172193463

theorem tailTrace_915392 : CollatzResearch.WordTrace tailWord_915392 prefixEnd_915392 313357388853725172193463 := by
  unfold tailWord_915392
  simp only [CollatzResearch.WordTrace]
  refine ⟨16693544549849297676062215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22258059399799063568082953 16693544549849297676062215)
  ·
    refine ⟨25040316824773946514093323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16693544549849297676062215 25040316824773946514093323)
    ·
      refine ⟨37560475237160919771139985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25040316824773946514093323 37560475237160919771139985)
      ·
        refine ⟨28170356427870689828354989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37560475237160919771139985 28170356427870689828354989)
        ·
          refine ⟨10563883660451508685633121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28170356427870689828354989 10563883660451508685633121)
          ·
            refine ⟨7922912745338631514224841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10563883660451508685633121 7922912745338631514224841)
            ·
              refine ⟨5942184559003973635668631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7922912745338631514224841 5942184559003973635668631)
              ·
                refine ⟨8913276838505960453502947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5942184559003973635668631 8913276838505960453502947)
                ·
                  refine ⟨13369915257758940680254421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8913276838505960453502947 13369915257758940680254421)
                  ·
                    refine ⟨313357388853725172193463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13369915257758940680254421 313357388853725172193463)
                    ·
                      rfl

theorem cell22_915392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 1, 7].length) (baseStart_915392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_915392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_915392 prefixEnd_915392 := by exact prefixLift 915392
  have htrace : WordTrace (prefixWord ++ tailWord_915392) baseStart_915392 baseEnd_915392 := by
    simpa [prefixWord, tailWord_915392, baseEnd_915392] using wordTrace_append hprefix tailTrace_915392
  have hstable : (prefixWord ++ tailWord_915392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915392).length < 2 ^ (prefixWord ++ tailWord_915392).sum := by decide
  have hdescent : baseEnd_915392 < baseStart_915392 := by decide
  rcases family_descends (prefixWord ++ tailWord_915392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915424 : List Nat := [2, 1, 1, 3, 1, 1, 1, 7, 1, 4]
def baseStart_915424 : Nat := 118140960795 + 915424 * 2 ^ 59
def prefixEnd_915424 : Nat := 4983230072969 + 3 ^ 40 * 915424 * 2
def baseEnd_915424 : Nat := 313368343107687755393365

theorem tailTrace_915424 : CollatzResearch.WordTrace tailWord_915424 prefixEnd_915424 313368343107687755393365 := by
  unfold tailWord_915424
  simp only [CollatzResearch.WordTrace]
  refine ⟨16694128117791332408644663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22258837490388443211526217 16694128117791332408644663)
  ·
    refine ⟨25041192176686998612966995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16694128117791332408644663 25041192176686998612966995)
    ·
      refine ⟨37561788265030497919450493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25041192176686998612966995 37561788265030497919450493)
      ·
        refine ⟨14085670599386436719793935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37561788265030497919450493 14085670599386436719793935)
        ·
          refine ⟨21128505899079655079690903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14085670599386436719793935 21128505899079655079690903)
          ·
            refine ⟨31692758848619482619536355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21128505899079655079690903 31692758848619482619536355)
            ·
              refine ⟨47539138272929223929304533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31692758848619482619536355 47539138272929223929304533)
              ·
                refine ⟨1114198553271778685843075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 47539138272929223929304533 1114198553271778685843075)
                ·
                  refine ⟨1671297829907668028764613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1114198553271778685843075 1671297829907668028764613)
                  ·
                    refine ⟨313368343107687755393365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1671297829907668028764613 313368343107687755393365)
                    ·
                      rfl

theorem cell22_915424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 7, 1, 4].length) (baseStart_915424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_915424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_915424 prefixEnd_915424 := by exact prefixLift 915424
  have htrace : WordTrace (prefixWord ++ tailWord_915424) baseStart_915424 baseEnd_915424 := by
    simpa [prefixWord, tailWord_915424, baseEnd_915424] using wordTrace_append hprefix tailTrace_915424
  have hstable : (prefixWord ++ tailWord_915424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915424).length < 2 ^ (prefixWord ++ tailWord_915424).sum := by decide
  have hdescent : baseEnd_915424 < baseStart_915424 := by decide
  rcases family_descends (prefixWord ++ tailWord_915424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915484 : List Nat := [2, 2, 3, 1, 3, 2, 9]
def baseStart_915484 : Nat := 118140960795 + 915484 * 2 ^ 59
def prefixEnd_915484 : Nat := 4983230072969 + 3 ^ 40 * 915484 * 2
def baseEnd_915484 : Nat := 11606995641995096255303

theorem tailTrace_915484 : CollatzResearch.WordTrace tailWord_915484 prefixEnd_915484 11606995641995096255303 := by
  unfold tailWord_915484
  simp only [CollatzResearch.WordTrace]
  refine ⟨16695222307682647532236753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22260296410243530042982337 16695222307682647532236753)
  ·
    refine ⟨12521416730761985649177565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16695222307682647532236753 12521416730761985649177565)
    ·
      refine ⟨4695531274035744618441587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12521416730761985649177565 4695531274035744618441587)
      ·
        refine ⟨7043296911053616927662381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4695531274035744618441587 7043296911053616927662381)
        ·
          refine ⟨2641236341645106347873393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7043296911053616927662381 2641236341645106347873393)
          ·
            refine ⟨1980927256233829760905045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2641236341645106347873393 1980927256233829760905045)
            ·
              refine ⟨11606995641995096255303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1980927256233829760905045 11606995641995096255303)
              ·
                rfl

theorem cell22_915484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 9].length) (baseStart_915484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_915484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_915484 prefixEnd_915484 := by exact prefixLift 915484
  have htrace : WordTrace (prefixWord ++ tailWord_915484) baseStart_915484 baseEnd_915484 := by
    simpa [prefixWord, tailWord_915484, baseEnd_915484] using wordTrace_append hprefix tailTrace_915484
  have hstable : (prefixWord ++ tailWord_915484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915484).length < 2 ^ (prefixWord ++ tailWord_915484).sum := by decide
  have hdescent : baseEnd_915484 < baseStart_915484 := by decide
  rcases family_descends (prefixWord ++ tailWord_915484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915516 : List Nat := [2, 2, 2, 2, 2, 1, 1, 4, 3, 3]
def baseStart_915516 : Nat := 118140960795 + 915516 * 2 ^ 59
def prefixEnd_915516 : Nat := 4983230072969 + 3 ^ 40 * 915516 * 2
def baseEnd_915516 : Nat := 313399836587830182093083

theorem tailTrace_915516 : CollatzResearch.WordTrace tailWord_915516 prefixEnd_915516 313399836587830182093083 := by
  unfold tailWord_915516
  simp only [CollatzResearch.WordTrace]
  refine ⟨16695805875624682264819201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22261074500832909686425601 16695805875624682264819201)
  ·
    refine ⟨12521854406718511698614401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16695805875624682264819201 12521854406718511698614401)
    ·
      refine ⟨9391390805038883773960801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12521854406718511698614401 9391390805038883773960801)
      ·
        refine ⟨7043543103779162830470601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9391390805038883773960801 7043543103779162830470601)
        ·
          refine ⟨5282657327834372122852951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7043543103779162830470601 5282657327834372122852951)
          ·
            refine ⟨7923985991751558184279427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5282657327834372122852951 7923985991751558184279427)
            ·
              refine ⟨11885978987627337276419141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7923985991751558184279427 11885978987627337276419141)
              ·
                refine ⟨2228621060180125739328589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11885978987627337276419141 2228621060180125739328589)
                ·
                  refine ⟨835732897567547152248221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2228621060180125739328589 835732897567547152248221)
                  ·
                    refine ⟨313399836587830182093083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 835732897567547152248221 313399836587830182093083)
                    ·
                      rfl

theorem cell22_915516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4, 3, 3].length) (baseStart_915516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_915516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_915516 prefixEnd_915516 := by exact prefixLift 915516
  have htrace : WordTrace (prefixWord ++ tailWord_915516) baseStart_915516 baseEnd_915516 := by
    simpa [prefixWord, tailWord_915516, baseEnd_915516] using wordTrace_append hprefix tailTrace_915516
  have hstable : (prefixWord ++ tailWord_915516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915516).length < 2 ^ (prefixWord ++ tailWord_915516).sum := by decide
  have hdescent : baseEnd_915516 < baseStart_915516 := by decide
  rcases family_descends (prefixWord ++ tailWord_915516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915593 : List Nat := [1, 2, 1, 1, 4, 2, 5, 1, 1, 4]
def baseStart_915593 : Nat := 118140960795 + 915593 * 2 ^ 59
def prefixEnd_915593 : Nat := 4983230072969 + 3 ^ 40 * 915593 * 2
def baseEnd_915593 : Nat := 313426195261427647917847

theorem tailTrace_915593 : CollatzResearch.WordTrace tailWord_915593 prefixEnd_915593 313426195261427647917847 := by
  unfold tailWord_915593
  simp only [CollatzResearch.WordTrace]
  refine ⟨33394420171970406680191433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22262946781313604453460955 33394420171970406680191433)
  ·
    refine ⟨25045815128977805010143575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33394420171970406680191433 25045815128977805010143575)
    ·
      refine ⟨37568722693466707515215363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25045815128977805010143575 37568722693466707515215363)
      ·
        refine ⟨56353084040200061272823045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37568722693466707515215363 56353084040200061272823045)
        ·
          refine ⟨10566203257537511488654321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56353084040200061272823045 10566203257537511488654321)
          ·
            refine ⟨7924652443153133616490741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10566203257537511488654321 7924652443153133616490741)
            ·
              refine ⟨742936166545606276546007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7924652443153133616490741 742936166545606276546007)
              ·
                refine ⟨1114404249818409414819011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 742936166545606276546007 1114404249818409414819011)
                ·
                  refine ⟨1671606374727614122228517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1114404249818409414819011 1671606374727614122228517)
                  ·
                    refine ⟨313426195261427647917847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1671606374727614122228517 313426195261427647917847)
                    ·
                      rfl

theorem cell22_915593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 1, 1, 4].length) (baseStart_915593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_915593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_915593 prefixEnd_915593 := by exact prefixLift 915593
  have htrace : WordTrace (prefixWord ++ tailWord_915593) baseStart_915593 baseEnd_915593 := by
    simpa [prefixWord, tailWord_915593, baseEnd_915593] using wordTrace_append hprefix tailTrace_915593
  have hstable : (prefixWord ++ tailWord_915593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915593).length < 2 ^ (prefixWord ++ tailWord_915593).sum := by decide
  have hdescent : baseEnd_915593 < baseStart_915593 := by decide
  rcases family_descends (prefixWord ++ tailWord_915593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915702 : List Nat := [5, 1, 1, 1, 1, 1, 5, 3, 1, 3]
def baseStart_915702 : Nat := 118140960795 + 915702 * 2 ^ 59
def prefixEnd_915702 : Nat := 4983230072969 + 3 ^ 40 * 915702 * 2
def baseEnd_915702 : Nat := 313463508188987696942513

theorem tailTrace_915702 : CollatzResearch.WordTrace tailWord_915702 prefixEnd_915702 313463508188987696942513 := by
  unfold tailWord_915702
  simp only [CollatzResearch.WordTrace]
  refine ⟨2087399733035969893494335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22265597152383678863939573 2087399733035969893494335)
  ·
    refine ⟨3131099599553954840241503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2087399733035969893494335 3131099599553954840241503)
    ·
      refine ⟨4696649399330932260362255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3131099599553954840241503 4696649399330932260362255)
      ·
        refine ⟨7044974098996398390543383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4696649399330932260362255 7044974098996398390543383)
        ·
          refine ⟨10567461148494597585815075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7044974098996398390543383 10567461148494597585815075)
          ·
            refine ⟨15851191722741896378722613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10567461148494597585815075 15851191722741896378722613)
            ·
              refine ⟨1486049224007052785505245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15851191722741896378722613 1486049224007052785505245)
              ·
                refine ⟨557268459002644794564467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1486049224007052785505245 557268459002644794564467)
                ·
                  refine ⟨835902688503967191846701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 557268459002644794564467 835902688503967191846701)
                  ·
                    refine ⟨313463508188987696942513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 835902688503967191846701 313463508188987696942513)
                    ·
                      rfl

theorem cell22_915702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 3, 1, 3].length) (baseStart_915702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_915702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_915702 prefixEnd_915702 := by exact prefixLift 915702
  have htrace : WordTrace (prefixWord ++ tailWord_915702) baseStart_915702 baseEnd_915702 := by
    simpa [prefixWord, tailWord_915702, baseEnd_915702] using wordTrace_append hprefix tailTrace_915702
  have hstable : (prefixWord ++ tailWord_915702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915702).length < 2 ^ (prefixWord ++ tailWord_915702).sum := by decide
  have hdescent : baseEnd_915702 < baseStart_915702 := by decide
  rcases family_descends (prefixWord ++ tailWord_915702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915719 : List Nat := [1, 1, 4, 5, 2, 1, 1, 1, 3, 3]
def baseStart_915719 : Nat := 118140960795 + 915719 * 2 ^ 59
def prefixEnd_915719 : Nat := 4983230072969 + 3 ^ 40 * 915719 * 2
def baseEnd_915719 : Nat := 313469327636405319267461

theorem tailTrace_915719 : CollatzResearch.WordTrace tailWord_915719 prefixEnd_915719 313469327636405319267461 := by
  unfold tailWord_915719
  simp only [CollatzResearch.WordTrace]
  refine ⟨33399015769513930199278211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22266010513009286799518807 33399015769513930199278211)
  ·
    refine ⟨50098523654270895298917317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33399015769513930199278211 50098523654270895298917317)
    ·
      refine ⟨9393473185175792868546997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50098523654270895298917317 9393473185175792868546997)
      ·
        refine ⟨880638111110230581426281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9393473185175792868546997 880638111110230581426281)
        ·
          refine ⟨660478583332672936069711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 880638111110230581426281 660478583332672936069711)
          ·
            refine ⟨990717874999009404104567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 660478583332672936069711 990717874999009404104567)
            ·
              refine ⟨1486076812498514106156851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 990717874999009404104567 1486076812498514106156851)
              ·
                refine ⟨2229115218747771159235277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1486076812498514106156851 2229115218747771159235277)
                ·
                  refine ⟨835918207030414184713229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2229115218747771159235277 835918207030414184713229)
                  ·
                    refine ⟨313469327636405319267461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 835918207030414184713229 313469327636405319267461)
                    ·
                      rfl

theorem cell22_915719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 1, 3, 3].length) (baseStart_915719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_915719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_915719 prefixEnd_915719 := by exact prefixLift 915719
  have htrace : WordTrace (prefixWord ++ tailWord_915719) baseStart_915719 baseEnd_915719 := by
    simpa [prefixWord, tailWord_915719, baseEnd_915719] using wordTrace_append hprefix tailTrace_915719
  have hstable : (prefixWord ++ tailWord_915719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915719).length < 2 ^ (prefixWord ++ tailWord_915719).sum := by decide
  have hdescent : baseEnd_915719 < baseStart_915719 := by decide
  rcases family_descends (prefixWord ++ tailWord_915719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915756 : List Nat := [2, 2, 1, 1, 1, 3, 2, 3, 1, 6]
def baseStart_915756 : Nat := 118140960795 + 915756 * 2 ^ 59
def prefixEnd_915756 : Nat := 4983230072969 + 3 ^ 40 * 915756 * 2
def baseEnd_915756 : Nat := 313481993492549556092347

theorem tailTrace_915756 : CollatzResearch.WordTrace tailWord_915756 prefixEnd_915756 313481993492549556092347 := by
  unfold tailWord_915756
  simp only [CollatzResearch.WordTrace]
  refine ⟨16700182635189942759187561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22266910180253257012250081 16700182635189942759187561)
  ·
    refine ⟨12525136976392457069390671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16700182635189942759187561 12525136976392457069390671)
    ·
      refine ⟨18787705464588685604086007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12525136976392457069390671 18787705464588685604086007)
      ·
        refine ⟨28181558196883028406129011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18787705464588685604086007 28181558196883028406129011)
        ·
          refine ⟨42272337295324542609193517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28181558196883028406129011 42272337295324542609193517)
          ·
            refine ⟨15852126485746703478447569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42272337295324542609193517 15852126485746703478447569)
            ·
              refine ⟨11889094864310027608835677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15852126485746703478447569 11889094864310027608835677)
              ·
                refine ⟨4458410574116260353313379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11889094864310027608835677 4458410574116260353313379)
                ·
                  refine ⟨6687615861174390529970069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4458410574116260353313379 6687615861174390529970069)
                  ·
                    refine ⟨313481993492549556092347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6687615861174390529970069 313481993492549556092347)
                    ·
                      rfl

theorem cell22_915756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 6].length) (baseStart_915756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_915756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_915756 prefixEnd_915756 := by exact prefixLift 915756
  have htrace : WordTrace (prefixWord ++ tailWord_915756) baseStart_915756 baseEnd_915756 := by
    simpa [prefixWord, tailWord_915756, baseEnd_915756] using wordTrace_append hprefix tailTrace_915756
  have hstable : (prefixWord ++ tailWord_915756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915756).length < 2 ^ (prefixWord ++ tailWord_915756).sum := by decide
  have hdescent : baseEnd_915756 < baseStart_915756 := by decide
  rcases family_descends (prefixWord ++ tailWord_915756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915762 : List Nat := [3, 2, 1, 1, 5, 1, 3, 1, 1, 4]
def baseStart_915762 : Nat := 118140960795 + 915762 * 2 ^ 59
def prefixEnd_915762 : Nat := 4983230072969 + 3 ^ 40 * 915762 * 2
def baseEnd_915762 : Nat := 313484047415167540442329

theorem tailTrace_915762 : CollatzResearch.WordTrace tailWord_915762 prefixEnd_915762 313484047415167540442329 := by
  unfold tailWord_915762
  simp only [CollatzResearch.WordTrace]
  refine ⟨8350146027089537135773385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22267056072238765695395693 8350146027089537135773385)
  ·
    refine ⟨6262609520317152851830039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8350146027089537135773385 6262609520317152851830039)
    ·
      refine ⟨9393914280475729277745059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6262609520317152851830039 9393914280475729277745059)
      ·
        refine ⟨14090871420713593916617589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9393914280475729277745059 14090871420713593916617589)
        ·
          refine ⟨1321019195691899429682899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14090871420713593916617589 1321019195691899429682899)
          ·
            refine ⟨1981528793537849144524349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1321019195691899429682899 1981528793537849144524349)
            ·
              refine ⟨743073297576693429196631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1981528793537849144524349 743073297576693429196631)
              ·
                refine ⟨1114609946365040143794947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 743073297576693429196631 1114609946365040143794947)
                ·
                  refine ⟨1671914919547560215692421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1114609946365040143794947 1671914919547560215692421)
                  ·
                    refine ⟨313484047415167540442329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1671914919547560215692421 313484047415167540442329)
                    ·
                      rfl

theorem cell22_915762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 1, 1, 4].length) (baseStart_915762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_915762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_915762 prefixEnd_915762 := by exact prefixLift 915762
  have htrace : WordTrace (prefixWord ++ tailWord_915762) baseStart_915762 baseEnd_915762 := by
    simpa [prefixWord, tailWord_915762, baseEnd_915762] using wordTrace_append hprefix tailTrace_915762
  have hstable : (prefixWord ++ tailWord_915762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915762).length < 2 ^ (prefixWord ++ tailWord_915762).sum := by decide
  have hdescent : baseEnd_915762 < baseStart_915762 := by decide
  rcases family_descends (prefixWord ++ tailWord_915762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915775 : List Nat := [1, 1, 2, 2, 4, 1, 4, 2, 2, 3]
def baseStart_915775 : Nat := 118140960795 + 915775 * 2 ^ 59
def prefixEnd_915775 : Nat := 4983230072969 + 3 ^ 40 * 915775 * 2
def baseEnd_915775 : Nat := 313488497580839839867289

theorem tailTrace_915775 : CollatzResearch.WordTrace tailWord_915775 prefixEnd_915775 313488497580839839867289 := by
  unfold tailWord_915775
  simp only [CollatzResearch.WordTrace]
  refine ⟨33401058257311051763316779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22267372171540701175544519 33401058257311051763316779)
  ·
    refine ⟨50101587385966577644975169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33401058257311051763316779 50101587385966577644975169)
    ·
      refine ⟨37576190539474933233731377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50101587385966577644975169 37576190539474933233731377)
      ·
        refine ⟨28182142904606199925298533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37576190539474933233731377 28182142904606199925298533)
        ·
          refine ⟨5284151794613662485993475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28182142904606199925298533 5284151794613662485993475)
          ·
            refine ⟨7926227691920493728990213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5284151794613662485993475 7926227691920493728990213)
            ·
              refine ⟨1486167692235092574185665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7926227691920493728990213 1486167692235092574185665)
              ·
                refine ⟨1114625769176319430639249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1486167692235092574185665 1114625769176319430639249)
                ·
                  refine ⟨835969326882239572979437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1114625769176319430639249 835969326882239572979437)
                  ·
                    refine ⟨313488497580839839867289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 835969326882239572979437 313488497580839839867289)
                    ·
                      rfl

theorem cell22_915775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 2, 2, 3].length) (baseStart_915775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_915775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_915775 prefixEnd_915775 := by exact prefixLift 915775
  have htrace : WordTrace (prefixWord ++ tailWord_915775) baseStart_915775 baseEnd_915775 := by
    simpa [prefixWord, tailWord_915775, baseEnd_915775] using wordTrace_append hprefix tailTrace_915775
  have hstable : (prefixWord ++ tailWord_915775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915775).length < 2 ^ (prefixWord ++ tailWord_915775).sum := by decide
  have hdescent : baseEnd_915775 < baseStart_915775 := by decide
  rcases family_descends (prefixWord ++ tailWord_915775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915777 : List Nat := [1, 2, 5, 2, 2, 1, 1, 4, 4]
def baseStart_915777 : Nat := 118140960795 + 915777 * 2 ^ 59
def prefixEnd_915777 : Nat := 4983230072969 + 3 ^ 40 * 915777 * 2
def baseEnd_915777 : Nat := 104496394073904167105761

theorem tailTrace_915777 : CollatzResearch.WordTrace tailWord_915777 prefixEnd_915777 104496394073904167105761 := by
  unfold tailWord_915777
  simp only [CollatzResearch.WordTrace]
  refine ⟨33401131203303806104889585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22267420802202537403259723 33401131203303806104889585)
  ·
    refine ⟨25050848402477854578667189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33401131203303806104889585 25050848402477854578667189)
    ·
      refine ⟨2348517037732298866750049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25050848402477854578667189 2348517037732298866750049)
      ·
        refine ⟨1761387778299224150062537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2348517037732298866750049 1761387778299224150062537)
        ·
          refine ⟨1321040833724418112546903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1761387778299224150062537 1321040833724418112546903)
          ·
            refine ⟨1981561250586627168820355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1321040833724418112546903 1981561250586627168820355)
            ·
              refine ⟨2972341875879940753230533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1981561250586627168820355 2972341875879940753230533)
              ·
                refine ⟨557314101727488891230725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2972341875879940753230533 557314101727488891230725)
                ·
                  refine ⟨104496394073904167105761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 557314101727488891230725 104496394073904167105761)
                  ·
                    rfl

theorem cell22_915777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 4, 4].length) (baseStart_915777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_915777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_915777 prefixEnd_915777 := by exact prefixLift 915777
  have htrace : WordTrace (prefixWord ++ tailWord_915777) baseStart_915777 baseEnd_915777 := by
    simpa [prefixWord, tailWord_915777, baseEnd_915777] using wordTrace_append hprefix tailTrace_915777
  have hstable : (prefixWord ++ tailWord_915777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915777).length < 2 ^ (prefixWord ++ tailWord_915777).sum := by decide
  have hdescent : baseEnd_915777 < baseStart_915777 := by decide
  rcases family_descends (prefixWord ++ tailWord_915777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915786 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 4, 7]
def baseStart_915786 : Nat := 118140960795 + 915786 * 2 ^ 59
def prefixEnd_915786 : Nat := 4983230072969 + 3 ^ 40 * 915786 * 2
def baseEnd_915786 : Nat := 313492263105639477842255

theorem tailTrace_915786 : CollatzResearch.WordTrace tailWord_915786 prefixEnd_915786 313492263105639477842255 := by
  unfold tailWord_915786
  simp only [CollatzResearch.WordTrace]
  refine ⟨8350364865067800160491803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22267639640180800427978141 8350364865067800160491803)
  ·
    refine ⟨12525547297601700240737705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8350364865067800160491803 12525547297601700240737705)
    ·
      refine ⟨9394160473201275180553279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12525547297601700240737705 9394160473201275180553279)
      ·
        refine ⟨14091240709801912770829919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9394160473201275180553279 14091240709801912770829919)
        ·
          refine ⟨21136861064702869156244879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14091240709801912770829919 21136861064702869156244879)
          ·
            refine ⟨31705291597054303734367319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21136861064702869156244879 31705291597054303734367319)
            ·
              refine ⟨47557937395581455601550979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31705291597054303734367319 47557937395581455601550979)
              ·
                refine ⟨71336906093372183402326469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47557937395581455601550979 71336906093372183402326469)
                ·
                  refine ⟨13375669892507284387936213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71336906093372183402326469 13375669892507284387936213)
                  ·
                    refine ⟨313492263105639477842255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13375669892507284387936213 313492263105639477842255)
                    ·
                      rfl

theorem cell22_915786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_915786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_915786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_915786 prefixEnd_915786 := by exact prefixLift 915786
  have htrace : WordTrace (prefixWord ++ tailWord_915786) baseStart_915786 baseEnd_915786 := by
    simpa [prefixWord, tailWord_915786, baseEnd_915786] using wordTrace_append hprefix tailTrace_915786
  have hstable : (prefixWord ++ tailWord_915786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915786).length < 2 ^ (prefixWord ++ tailWord_915786).sum := by decide
  have hdescent : baseEnd_915786 < baseStart_915786 := by decide
  rcases family_descends (prefixWord ++ tailWord_915786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915801 : List Nat := [1, 2, 1, 2, 2, 2, 1, 1, 4, 6]
def baseStart_915801 : Nat := 118140960795 + 915801 * 2 ^ 59
def prefixEnd_915801 : Nat := 4983230072969 + 3 ^ 40 * 915801 * 2
def baseEnd_915801 : Nat := 313497397912184438717209

theorem tailTrace_915801 : CollatzResearch.WordTrace tailWord_915801 prefixEnd_915801 313497397912184438717209 := by
  unfold tailWord_915801
  simp only [CollatzResearch.WordTrace]
  refine ⟨33402006555216858203763257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22268004370144572135842171 33402006555216858203763257)
  ·
    refine ⟨25051504916412643652822443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33402006555216858203763257 25051504916412643652822443)
    ·
      refine ⟨37577257374618965479233665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25051504916412643652822443 37577257374618965479233665)
      ·
        refine ⟨28182943030964224109425249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37577257374618965479233665 28182943030964224109425249)
        ·
          refine ⟨21137207273223168082068937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28182943030964224109425249 21137207273223168082068937)
          ·
            refine ⟨15852905454917376061551703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21137207273223168082068937 15852905454917376061551703)
            ·
              refine ⟨23779358182376064092327555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15852905454917376061551703 23779358182376064092327555)
              ·
                refine ⟨35669037273564096138491333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23779358182376064092327555 35669037273564096138491333)
                ·
                  refine ⟨6687944488793268025967125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35669037273564096138491333 6687944488793268025967125)
                  ·
                    refine ⟨313497397912184438717209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6687944488793268025967125 313497397912184438717209)
                    ·
                      rfl

theorem cell22_915801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 6].length) (baseStart_915801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_915801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_915801 prefixEnd_915801 := by exact prefixLift 915801
  have htrace : WordTrace (prefixWord ++ tailWord_915801) baseStart_915801 baseEnd_915801 := by
    simpa [prefixWord, tailWord_915801, baseEnd_915801] using wordTrace_append hprefix tailTrace_915801
  have hstable : (prefixWord ++ tailWord_915801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915801).length < 2 ^ (prefixWord ++ tailWord_915801).sum := by decide
  have hdescent : baseEnd_915801 < baseStart_915801 := by decide
  rcases family_descends (prefixWord ++ tailWord_915801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915837 : List Nat := [1, 4, 1, 1, 2, 3, 2, 4, 1, 3]
def baseStart_915837 : Nat := 118140960795 + 915837 * 2 ^ 59
def prefixEnd_915837 : Nat := 4983230072969 + 3 ^ 40 * 915837 * 2
def baseEnd_915837 : Nat := 313509721447892344817099

theorem tailTrace_915837 : CollatzResearch.WordTrace tailWord_915837 prefixEnd_915837 313509721447892344817099 := by
  unfold tailWord_915837
  simp only [CollatzResearch.WordTrace]
  refine ⟨33403319583086436352073765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22268879722057624234715843 33403319583086436352073765)
  ·
    refine ⟨6263122421828706816013831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33403319583086436352073765 6263122421828706816013831)
    ·
      refine ⟨9394683632743060224020747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6263122421828706816013831 9394683632743060224020747)
      ·
        refine ⟨14092025449114590336031121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9394683632743060224020747 14092025449114590336031121)
        ·
          refine ⟨10569019086835942752023341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14092025449114590336031121 10569019086835942752023341)
          ·
            refine ⟨3963382157563478532008753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10569019086835942752023341 3963382157563478532008753)
            ·
              refine ⟨2972536618172608899006565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3963382157563478532008753 2972536618172608899006565)
              ·
                refine ⟨557350615907364168563731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2972536618172608899006565 557350615907364168563731)
                ·
                  refine ⟨836025923861046252845597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 557350615907364168563731 836025923861046252845597)
                  ·
                    refine ⟨313509721447892344817099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 836025923861046252845597 313509721447892344817099)
                    ·
                      rfl

theorem cell22_915837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 4, 1, 3].length) (baseStart_915837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_915837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_915837 prefixEnd_915837 := by exact prefixLift 915837
  have htrace : WordTrace (prefixWord ++ tailWord_915837) baseStart_915837 baseEnd_915837 := by
    simpa [prefixWord, tailWord_915837, baseEnd_915837] using wordTrace_append hprefix tailTrace_915837
  have hstable : (prefixWord ++ tailWord_915837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915837).length < 2 ^ (prefixWord ++ tailWord_915837).sum := by decide
  have hdescent : baseEnd_915837 < baseStart_915837 := by decide
  rcases family_descends (prefixWord ++ tailWord_915837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915848 : List Nat := [2, 1, 3, 3, 1, 1, 1, 3, 2, 5]
def baseStart_915848 : Nat := 118140960795 + 915848 * 2 ^ 59
def prefixEnd_915848 : Nat := 4983230072969 + 3 ^ 40 * 915848 * 2
def baseEnd_915848 : Nat := 313513486972691982792065

theorem tailTrace_915848 : CollatzResearch.WordTrace tailWord_915848 prefixEnd_915848 313513486972691982792065 := by
  unfold tailWord_915848
  simp only [CollatzResearch.WordTrace]
  refine ⟨16701860393023292615362099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22269147190697723487149465 16701860393023292615362099)
  ·
    refine ⟨25052790589534938923043149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16701860393023292615362099 25052790589534938923043149)
    ·
      refine ⟨9394796471075602096141181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25052790589534938923043149 9394796471075602096141181)
      ·
        refine ⟨3523048676653350786052943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9394796471075602096141181 3523048676653350786052943)
        ·
          refine ⟨5284573014980026179079415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3523048676653350786052943 5284573014980026179079415)
          ·
            refine ⟨7926859522470039268619123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5284573014980026179079415 7926859522470039268619123)
            ·
              refine ⟨11890289283705058902928685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7926859522470039268619123 11890289283705058902928685)
              ·
                refine ⟨4458858481389397088598257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11890289283705058902928685 4458858481389397088598257)
                ·
                  refine ⟨3344143861042047816448693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4458858481389397088598257 3344143861042047816448693)
                  ·
                    refine ⟨313513486972691982792065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3344143861042047816448693 313513486972691982792065)
                    ·
                      rfl

theorem cell22_915848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_915848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_915848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_915848 prefixEnd_915848 := by exact prefixLift 915848
  have htrace : WordTrace (prefixWord ++ tailWord_915848) baseStart_915848 baseEnd_915848 := by
    simpa [prefixWord, tailWord_915848, baseEnd_915848] using wordTrace_append hprefix tailTrace_915848
  have hstable : (prefixWord ++ tailWord_915848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915848).length < 2 ^ (prefixWord ++ tailWord_915848).sum := by decide
  have hdescent : baseEnd_915848 < baseStart_915848 := by decide
  rcases family_descends (prefixWord ++ tailWord_915848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915863 : List Nat := [1, 1, 3, 3, 1, 1, 2, 3, 3, 4]
def baseStart_915863 : Nat := 118140960795 + 915863 * 2 ^ 59
def prefixEnd_915863 : Nat := 4983230072969 + 3 ^ 40 * 915863 * 2
def baseEnd_915863 : Nat := 313518621779236943667019

theorem tailTrace_915863 : CollatzResearch.WordTrace tailWord_915863 prefixEnd_915863 313518621779236943667019 := by
  unfold tailWord_915863
  simp only [CollatzResearch.WordTrace]
  refine ⟨33404267880992242792520243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22269511920661495195013495 33404267880992242792520243)
  ·
    refine ⟨50106401821488364188780365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33404267880992242792520243 50106401821488364188780365)
    ·
      refine ⟨18789900683058136570792637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50106401821488364188780365 18789900683058136570792637)
      ·
        refine ⟨7046212756146801214047239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18789900683058136570792637 7046212756146801214047239)
        ·
          refine ⟨10569319134220201821070859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7046212756146801214047239 10569319134220201821070859)
          ·
            refine ⟨15853978701330302731606289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10569319134220201821070859 15853978701330302731606289)
            ·
              refine ⟨11890484025997727048704717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15853978701330302731606289 11890484025997727048704717)
              ·
                refine ⟨4458931509749147643264269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11890484025997727048704717 4458931509749147643264269)
                ·
                  refine ⟨1672099316155930366224101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4458931509749147643264269 1672099316155930366224101)
                  ·
                    refine ⟨313518621779236943667019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1672099316155930366224101 313518621779236943667019)
                    ·
                      rfl

theorem cell22_915863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 3, 4].length) (baseStart_915863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_915863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_915863 prefixEnd_915863 := by exact prefixLift 915863
  have htrace : WordTrace (prefixWord ++ tailWord_915863) baseStart_915863 baseEnd_915863 := by
    simpa [prefixWord, tailWord_915863, baseEnd_915863] using wordTrace_append hprefix tailTrace_915863
  have hstable : (prefixWord ++ tailWord_915863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915863).length < 2 ^ (prefixWord ++ tailWord_915863).sum := by decide
  have hdescent : baseEnd_915863 < baseStart_915863 := by decide
  rcases family_descends (prefixWord ++ tailWord_915863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915895 : List Nat := [1, 1, 3, 1, 3, 5, 1, 1, 6]
def baseStart_915895 : Nat := 118140960795 + 915895 * 2 ^ 59
def prefixEnd_915895 : Nat := 4983230072969 + 3 ^ 40 * 915895 * 2
def baseEnd_915895 : Nat := 104509858677733175622307

theorem tailTrace_915895 : CollatzResearch.WordTrace tailWord_915895 prefixEnd_915895 104509858677733175622307 := by
  unfold tailWord_915895
  simp only [CollatzResearch.WordTrace]
  refine ⟨33405435016876312257685139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22270290011250874838456759 33405435016876312257685139)
  ·
    refine ⟨50108152525314468386527709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33405435016876312257685139 50108152525314468386527709)
    ·
      refine ⟨18790557196992925644947891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50108152525314468386527709 18790557196992925644947891)
      ·
        refine ⟨28185835795489388467421837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18790557196992925644947891 28185835795489388467421837)
        ·
          refine ⟨10569688423308520675283189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28185835795489388467421837 10569688423308520675283189)
          ·
            refine ⟨990908289685173813307799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10569688423308520675283189 990908289685173813307799)
            ·
              refine ⟨1486362434527760719961699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 990908289685173813307799 1486362434527760719961699)
              ·
                refine ⟨2229543651791641079942549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1486362434527760719961699 2229543651791641079942549)
                ·
                  refine ⟨104509858677733175622307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2229543651791641079942549 104509858677733175622307)
                  ·
                    rfl

theorem cell22_915895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 1, 6].length) (baseStart_915895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_915895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_915895 prefixEnd_915895 := by exact prefixLift 915895
  have htrace : WordTrace (prefixWord ++ tailWord_915895) baseStart_915895 baseEnd_915895 := by
    simpa [prefixWord, tailWord_915895, baseEnd_915895] using wordTrace_append hprefix tailTrace_915895
  have hstable : (prefixWord ++ tailWord_915895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915895).length < 2 ^ (prefixWord ++ tailWord_915895).sum := by decide
  have hdescent : baseEnd_915895 < baseStart_915895 := by decide
  rcases family_descends (prefixWord ++ tailWord_915895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915925 : List Nat := [1, 3, 2, 3, 1, 2, 1, 3, 2, 4]
def baseStart_915925 : Nat := 118140960795 + 915925 * 2 ^ 59
def prefixEnd_915925 : Nat := 4983230072969 + 3 ^ 40 * 915925 * 2
def baseEnd_915925 : Nat := 313539845646289448616829

theorem tailTrace_915925 : CollatzResearch.WordTrace tailWord_915925 prefixEnd_915925 313539845646289448616829 := by
  unfold tailWord_915925
  simp only [CollatzResearch.WordTrace]
  refine ⟨33406529206767627381277229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22271019471178418254184819 33406529206767627381277229)
  ·
    refine ⟨12527448452537860267978961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33406529206767627381277229 12527448452537860267978961)
    ·
      refine ⟨9395586339403395200984221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12527448452537860267978961 9395586339403395200984221)
      ·
        refine ⟨3523344877276273200369083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9395586339403395200984221 3523344877276273200369083)
        ·
          refine ⟨5285017315914409800553625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3523344877276273200369083 5285017315914409800553625)
          ·
            refine ⟨3963762986935807350415219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5285017315914409800553625 3963762986935807350415219)
            ·
              refine ⟨5945644480403711025622829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3963762986935807350415219 5945644480403711025622829)
              ·
                refine ⟨2229616680151391634608561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5945644480403711025622829 2229616680151391634608561)
                ·
                  refine ⟨1672212510113543725956421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2229616680151391634608561 1672212510113543725956421)
                  ·
                    refine ⟨313539845646289448616829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1672212510113543725956421 313539845646289448616829)
                    ·
                      rfl

theorem cell22_915925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_915925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_915925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_915925 prefixEnd_915925 := by exact prefixLift 915925
  have htrace : WordTrace (prefixWord ++ tailWord_915925) baseStart_915925 baseEnd_915925 := by
    simpa [prefixWord, tailWord_915925, baseEnd_915925] using wordTrace_append hprefix tailTrace_915925
  have hstable : (prefixWord ++ tailWord_915925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915925).length < 2 ^ (prefixWord ++ tailWord_915925).sum := by decide
  have hdescent : baseEnd_915925 < baseStart_915925 := by decide
  rcases family_descends (prefixWord ++ tailWord_915925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
