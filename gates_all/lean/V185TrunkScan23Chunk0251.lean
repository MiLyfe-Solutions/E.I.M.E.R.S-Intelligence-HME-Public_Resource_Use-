import V185TrunkScan23Chunk0250

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1485348 : List Nat := [2, 3, 1, 5, 1, 1, 1, 2, 7]
def baseStart_1485348 : Nat := 118140960795 + 1485348 * 2 ^ 59
def prefixEnd_1485348 : Nat := 4983230072969 + 3 ^ 40 * 1485348 * 2
def baseEnd_1485348 : Nat := 84744162577173311424335

theorem tailTrace_1485348 : CollatzResearch.WordTrace tailWord_1485348 prefixEnd_1485348 84744162577173311424335 := by
  unfold tailWord_1485348
  simp only [CollatzResearch.WordTrace]
  refine ⟨27087546111422674043616349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36116728148563565391488465 27087546111422674043616349)
  ·
    refine ⟨10157829791783502766356131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27087546111422674043616349 10157829791783502766356131)
    ·
      refine ⟨15236744687675254149534197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10157829791783502766356131 15236744687675254149534197)
      ·
        refine ⟨1428444814469555076518831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15236744687675254149534197 1428444814469555076518831)
        ·
          refine ⟨2142667221704332614778247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1428444814469555076518831 2142667221704332614778247)
          ·
            refine ⟨3214000832556498922167371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2142667221704332614778247 3214000832556498922167371)
            ·
              refine ⟨4821001248834748383251057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3214000832556498922167371 4821001248834748383251057)
              ·
                refine ⟨3615750936626061287438293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4821001248834748383251057 3615750936626061287438293)
                ·
                  refine ⟨84744162577173311424335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3615750936626061287438293 84744162577173311424335)
                  ·
                    rfl

theorem cell23_1485348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 2, 7].length) (baseStart_1485348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1485348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1485348 prefixEnd_1485348 := by exact prefixLift 1485348
  have htrace : WordTrace (prefixWord ++ tailWord_1485348) baseStart_1485348 baseEnd_1485348 := by
    simpa [prefixWord, tailWord_1485348, baseEnd_1485348] using wordTrace_append hprefix tailTrace_1485348
  have hstable : (prefixWord ++ tailWord_1485348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485348).length < 2 ^ (prefixWord ++ tailWord_1485348).sum := by decide
  have hdescent : baseEnd_1485348 < baseStart_1485348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485361 : List Nat := [1, 2, 2, 3, 1, 1, 5, 1, 2, 5]
def baseStart_1485361 : Nat := 118140960795 + 1485361 * 2 ^ 59
def prefixEnd_1485361 : Nat := 4983230072969 + 3 ^ 40 * 1485361 * 2
def baseEnd_1485361 : Nat := 254234712814356083985485

theorem tailTrace_1485361 : CollatzResearch.WordTrace tailWord_1485361 prefixEnd_1485361 254234712814356083985485 := by
  unfold tailWord_1485361
  simp only [CollatzResearch.WordTrace]
  refine ⟨54175566371798251307455937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36117044247865500871637291 54175566371798251307455937)
  ·
    refine ⟨40631674778848688480591953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54175566371798251307455937 40631674778848688480591953)
    ·
      refine ⟨30473756084136516360443965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40631674778848688480591953 30473756084136516360443965)
      ·
        refine ⟨11427658531551193635166487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30473756084136516360443965 11427658531551193635166487)
        ·
          refine ⟨17141487797326790452749731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11427658531551193635166487 17141487797326790452749731)
          ·
            refine ⟨25712231695990185679124597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17141487797326790452749731 25712231695990185679124597)
            ·
              refine ⟨2410521721499079907417931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25712231695990185679124597 2410521721499079907417931)
              ·
                refine ⟨3615782582248619861126897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2410521721499079907417931 3615782582248619861126897)
                ·
                  refine ⟨2711836936686464895845173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3615782582248619861126897 2711836936686464895845173)
                  ·
                    refine ⟨254234712814356083985485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2711836936686464895845173 254234712814356083985485)
                    ·
                      rfl

theorem cell23_1485361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 1, 2, 5].length) (baseStart_1485361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1485361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1485361 prefixEnd_1485361 := by exact prefixLift 1485361
  have htrace : WordTrace (prefixWord ++ tailWord_1485361) baseStart_1485361 baseEnd_1485361 := by
    simpa [prefixWord, tailWord_1485361, baseEnd_1485361] using wordTrace_append hprefix tailTrace_1485361
  have hstable : (prefixWord ++ tailWord_1485361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485361).length < 2 ^ (prefixWord ++ tailWord_1485361).sum := by decide
  have hdescent : baseEnd_1485361 < baseStart_1485361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485384 : List Nat := [2, 1, 3, 1, 1, 1, 1, 3, 2, 3, 5]
def baseStart_1485384 : Nat := 118140960795 + 1485384 * 2 ^ 59
def prefixEnd_1485384 : Nat := 4983230072969 + 3 ^ 40 * 1485384 * 2
def baseEnd_1485384 : Nat := 762715948498121661968849

theorem tailTrace_1485384 : CollatzResearch.WordTrace tailWord_1485384 prefixEnd_1485384 762715948498121661968849 := by
  unfold tailWord_1485384
  simp only [CollatzResearch.WordTrace]
  refine ⟨27088202625357463117771603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36117603500476617490362137 27088202625357463117771603)
  ·
    refine ⟨40632303938036194676657405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27088202625357463117771603 40632303938036194676657405)
    ·
      refine ⟨15237113976763573003746527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40632303938036194676657405 15237113976763573003746527)
      ·
        refine ⟨22855670965145359505619791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15237113976763573003746527 22855670965145359505619791)
        ·
          refine ⟨34283506447718039258429687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22855670965145359505619791 34283506447718039258429687)
          ·
            refine ⟨51425259671577058887644531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34283506447718039258429687 51425259671577058887644531)
            ·
              refine ⟨77137889507365588331466797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51425259671577058887644531 77137889507365588331466797)
              ·
                refine ⟨28926708565262095624300049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77137889507365588331466797 28926708565262095624300049)
                ·
                  refine ⟨21695031423946571718225037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28926708565262095624300049 21695031423946571718225037)
                  ·
                    refine ⟨8135636783979964394334389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21695031423946571718225037 8135636783979964394334389)
                    ·
                      refine ⟨762715948498121661968849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8135636783979964394334389 762715948498121661968849)
                      ·
                        rfl

theorem cell23_1485384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_1485384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1485384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1485384 prefixEnd_1485384 := by exact prefixLift 1485384
  have htrace : WordTrace (prefixWord ++ tailWord_1485384) baseStart_1485384 baseEnd_1485384 := by
    simpa [prefixWord, tailWord_1485384, baseEnd_1485384] using wordTrace_append hprefix tailTrace_1485384
  have hstable : (prefixWord ++ tailWord_1485384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485384).length < 2 ^ (prefixWord ++ tailWord_1485384).sum := by decide
  have hdescent : baseEnd_1485384 < baseStart_1485384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485391 : List Nat := [1, 1, 2, 1, 1, 2, 5, 3, 3, 4]
def baseStart_1485391 : Nat := 118140960795 + 1485391 * 2 ^ 59
def prefixEnd_1485391 : Nat := 4983230072969 + 3 ^ 40 * 1485391 * 2
def baseEnd_1485391 : Nat := 254239847620901044860439

theorem tailTrace_1485391 : CollatzResearch.WordTrace tailWord_1485391 prefixEnd_1485391 254239847620901044860439 := by
  unfold tailWord_1485391
  simp only [CollatzResearch.WordTrace]
  refine ⟨54176660561689566431048027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36117773707793044287365351 54176660561689566431048027)
  ·
    refine ⟨81264990842534349646572041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54176660561689566431048027 81264990842534349646572041)
    ·
      refine ⟨60948743131900762234929031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81264990842534349646572041 60948743131900762234929031)
      ·
        refine ⟨91423114697851143352393547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60948743131900762234929031 91423114697851143352393547)
        ·
          refine ⟨137134672046776715028590321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91423114697851143352393547 137134672046776715028590321)
          ·
            refine ⟨102851004035082536271442741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137134672046776715028590321 102851004035082536271442741)
            ·
              refine ⟨9642281628288987775447757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 102851004035082536271442741 9642281628288987775447757)
              ·
                refine ⟨3615855610608370415792909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9642281628288987775447757 3615855610608370415792909)
                ·
                  refine ⟨1355945853978138905922341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3615855610608370415792909 1355945853978138905922341)
                  ·
                    refine ⟨254239847620901044860439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1355945853978138905922341 254239847620901044860439)
                    ·
                      rfl

theorem cell23_1485391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3, 3, 4].length) (baseStart_1485391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1485391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1485391 prefixEnd_1485391 := by exact prefixLift 1485391
  have htrace : WordTrace (prefixWord ++ tailWord_1485391) baseStart_1485391 baseEnd_1485391 := by
    simpa [prefixWord, tailWord_1485391, baseEnd_1485391] using wordTrace_append hprefix tailTrace_1485391
  have hstable : (prefixWord ++ tailWord_1485391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485391).length < 2 ^ (prefixWord ++ tailWord_1485391).sum := by decide
  have hdescent : baseEnd_1485391 < baseStart_1485391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485418 : List Nat := [3, 1, 3, 2, 1, 1, 2, 3, 2, 2, 3]
def baseStart_1485418 : Nat := 118140960795 + 1485418 * 2 ^ 59
def prefixEnd_1485418 : Nat := 4983230072969 + 3 ^ 40 * 1485418 * 2
def baseEnd_1485418 : Nat := 762733406840374528943693

theorem tailTrace_1485418 : CollatzResearch.WordTrace tailWord_1485418 prefixEnd_1485418 762733406840374528943693 := by
  unfold tailWord_1485418
  simp only [CollatzResearch.WordTrace]
  refine ⟨13544411333147937510570227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36118430221727833361520605 13544411333147937510570227)
  ·
    refine ⟨20316616999721906265855341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13544411333147937510570227 20316616999721906265855341)
    ·
      refine ⟨7618731374895714849695753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20316616999721906265855341 7618731374895714849695753)
      ·
        refine ⟨5714048531171786137271815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7618731374895714849695753 5714048531171786137271815)
        ·
          refine ⟨8571072796757679205907723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5714048531171786137271815 8571072796757679205907723)
          ·
            refine ⟨12856609195136518808861585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8571072796757679205907723 12856609195136518808861585)
            ·
              refine ⟨9642456896352389106646189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12856609195136518808861585 9642456896352389106646189)
              ·
                refine ⟨3615921336132145914992321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9642456896352389106646189 3615921336132145914992321)
                ·
                  refine ⟨2711941002099109436244241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3615921336132145914992321 2711941002099109436244241)
                  ·
                    refine ⟨2033955751574332077183181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2711941002099109436244241 2033955751574332077183181)
                    ·
                      refine ⟨762733406840374528943693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2033955751574332077183181 762733406840374528943693)
                      ·
                        rfl

theorem cell23_1485418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_1485418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1485418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1485418 prefixEnd_1485418 := by exact prefixLift 1485418
  have htrace : WordTrace (prefixWord ++ tailWord_1485418) baseStart_1485418 baseEnd_1485418 := by
    simpa [prefixWord, tailWord_1485418, baseEnd_1485418] using wordTrace_append hprefix tailTrace_1485418
  have hstable : (prefixWord ++ tailWord_1485418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485418).length < 2 ^ (prefixWord ++ tailWord_1485418).sum := by decide
  have hdescent : baseEnd_1485418 < baseStart_1485418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485421 : List Nat := [1, 5, 1, 1, 3, 1, 1, 2, 8]
def baseStart_1485421 : Nat := 118140960795 + 1485421 * 2 ^ 59
def prefixEnd_1485421 : Nat := 4983230072969 + 3 ^ 40 * 1485421 * 2
def baseEnd_1485421 : Nat := 84748327475815335245131

theorem tailTrace_1485421 : CollatzResearch.WordTrace tailWord_1485421 prefixEnd_1485421 84748327475815335245131 := by
  unfold tailWord_1485421
  simp only [CollatzResearch.WordTrace]
  refine ⟨54177754751580881554640117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36118503167720587703093411 54177754751580881554640117)
  ·
    refine ⟨5079164507960707645747511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54177754751580881554640117 5079164507960707645747511)
    ·
      refine ⟨7618746761941061468621267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5079164507960707645747511 7618746761941061468621267)
      ·
        refine ⟨11428120142911592202931901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7618746761941061468621267 11428120142911592202931901)
        ·
          refine ⟨4285545053591847076099463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11428120142911592202931901 4285545053591847076099463)
          ·
            refine ⟨6428317580387770614149195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4285545053591847076099463 6428317580387770614149195)
            ·
              refine ⟨9642476370581655921223793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6428317580387770614149195 9642476370581655921223793)
              ·
                refine ⟨7231857277936241940917845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9642476370581655921223793 7231857277936241940917845)
                ·
                  refine ⟨84748327475815335245131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7231857277936241940917845 84748327475815335245131)
                  ·
                    rfl

theorem cell23_1485421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 8].length) (baseStart_1485421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1485421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1485421 prefixEnd_1485421 := by exact prefixLift 1485421
  have htrace : WordTrace (prefixWord ++ tailWord_1485421) baseStart_1485421 baseEnd_1485421 := by
    simpa [prefixWord, tailWord_1485421, baseEnd_1485421] using wordTrace_append hprefix tailTrace_1485421
  have hstable : (prefixWord ++ tailWord_1485421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485421).length < 2 ^ (prefixWord ++ tailWord_1485421).sum := by decide
  have hdescent : baseEnd_1485421 < baseStart_1485421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485434 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 1, 11]
def baseStart_1485434 : Nat := 118140960795 + 1485434 * 2 ^ 59
def prefixEnd_1485434 : Nat := 4983230072969 + 3 ^ 40 * 1485434 * 2
def baseEnd_1485434 : Nat := 254247207510282155447873

theorem tailTrace_1485434 : CollatzResearch.WordTrace tailWord_1485434 prefixEnd_1485434 254247207510282155447873 := by
  unfold tailWord_1485434
  simp only [CollatzResearch.WordTrace]
  refine ⟨13544557225133446193715839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36118819267022523183242237 13544557225133446193715839)
  ·
    refine ⟨20316835837700169290573759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13544557225133446193715839 20316835837700169290573759)
    ·
      refine ⟨30475253756550253935860639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20316835837700169290573759 30475253756550253935860639)
      ·
        refine ⟨45712880634825380903790959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30475253756550253935860639 45712880634825380903790959)
        ·
          refine ⟨68569320952238071355686439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45712880634825380903790959 68569320952238071355686439)
          ·
            refine ⟨102853981428357107033529659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68569320952238071355686439 102853981428357107033529659)
            ·
              refine ⟨154280972142535660550294489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102853981428357107033529659 154280972142535660550294489)
              ·
                refine ⟨115710729106901745412720867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154280972142535660550294489 115710729106901745412720867)
                ·
                  refine ⟨173566093660352618119081301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115710729106901745412720867 173566093660352618119081301)
                  ·
                    refine ⟨254247207510282155447873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 173566093660352618119081301 254247207510282155447873)
                    ·
                      rfl

theorem cell23_1485434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 1, 11].length) (baseStart_1485434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1485434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1485434 prefixEnd_1485434 := by exact prefixLift 1485434
  have htrace : WordTrace (prefixWord ++ tailWord_1485434) baseStart_1485434 baseEnd_1485434 := by
    simpa [prefixWord, tailWord_1485434, baseEnd_1485434] using wordTrace_append hprefix tailTrace_1485434
  have hstable : (prefixWord ++ tailWord_1485434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485434).length < 2 ^ (prefixWord ++ tailWord_1485434).sum := by decide
  have hdescent : baseEnd_1485434 < baseStart_1485434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485468 : List Nat := [2, 2, 3, 2, 2, 2, 1, 1, 3, 5]
def baseStart_1485468 : Nat := 118140960795 + 1485468 * 2 ^ 59
def prefixEnd_1485468 : Nat := 4983230072969 + 3 ^ 40 * 1485468 * 2
def baseEnd_1485468 : Nat := 254253026957699777772821

theorem tailTrace_1485468 : CollatzResearch.WordTrace tailWord_1485468 prefixEnd_1485468 254253026957699777772821 := by
  unfold tailWord_1485468
  simp only [CollatzResearch.WordTrace]
  refine ⟨27089734491205304290800529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36119645988273739054400705 27089734491205304290800529)
  ·
    refine ⟨20317300868403978218100397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27089734491205304290800529 20317300868403978218100397)
    ·
      refine ⟨7618987825651491831787649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20317300868403978218100397 7618987825651491831787649)
      ·
        refine ⟨5714240869238618873840737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7618987825651491831787649 5714240869238618873840737)
        ·
          refine ⟨4285680651928964155380553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5714240869238618873840737 4285680651928964155380553)
          ·
            refine ⟨3214260488946723116535415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4285680651928964155380553 3214260488946723116535415)
            ·
              refine ⟨4821390733420084674803123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3214260488946723116535415 4821390733420084674803123)
              ·
                refine ⟨7232086100130127012204685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4821390733420084674803123 7232086100130127012204685)
                ·
                  refine ⟨2712032287548797629576757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7232086100130127012204685 2712032287548797629576757)
                  ·
                    refine ⟨254253026957699777772821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2712032287548797629576757 254253026957699777772821)
                    ·
                      rfl

theorem cell23_1485468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_1485468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1485468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1485468 prefixEnd_1485468 := by exact prefixLift 1485468
  have htrace : WordTrace (prefixWord ++ tailWord_1485468) baseStart_1485468 baseEnd_1485468 := by
    simpa [prefixWord, tailWord_1485468, baseEnd_1485468] using wordTrace_append hprefix tailTrace_1485468
  have hstable : (prefixWord ++ tailWord_1485468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485468).length < 2 ^ (prefixWord ++ tailWord_1485468).sum := by decide
  have hdescent : baseEnd_1485468 < baseStart_1485468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485518 : List Nat := [4, 1, 1, 1, 3, 2, 1, 3, 1, 2, 4]
def baseStart_1485518 : Nat := 118140960795 + 1485518 * 2 ^ 59
def prefixEnd_1485518 : Nat := 4983230072969 + 3 ^ 40 * 1485518 * 2
def baseEnd_1485518 : Nat := 762784754905824137693233

theorem tailTrace_1485518 : CollatzResearch.WordTrace tailWord_1485518 prefixEnd_1485518 762784754905824137693233 := by
  unfold tailWord_1485518
  simp only [CollatzResearch.WordTrace]
  refine ⟨6772661579028683390115151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36120861754819644747280805 6772661579028683390115151)
  ·
    refine ⟨10158992368543025085172727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6772661579028683390115151 10158992368543025085172727)
    ·
      refine ⟨15238488552814537627759091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10158992368543025085172727 15238488552814537627759091)
      ·
        refine ⟨22857732829221806441638637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15238488552814537627759091 22857732829221806441638637)
        ·
          refine ⟨8571649810958177415614489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22857732829221806441638637 8571649810958177415614489)
          ·
            refine ⟨6428737358218633061710867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8571649810958177415614489 6428737358218633061710867)
            ·
              refine ⟨9643106037327949592566301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6428737358218633061710867 9643106037327949592566301)
              ·
                refine ⟨3616164763997981097212363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9643106037327949592566301 3616164763997981097212363)
                ·
                  refine ⟨5424247145996971645818545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3616164763997981097212363 5424247145996971645818545)
                  ·
                    refine ⟨4068185359497728734363909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5424247145996971645818545 4068185359497728734363909)
                    ·
                      refine ⟨762784754905824137693233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4068185359497728734363909 762784754905824137693233)
                      ·
                        rfl

theorem cell23_1485518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3, 1, 2, 4].length) (baseStart_1485518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1485518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1485518 prefixEnd_1485518 := by exact prefixLift 1485518
  have htrace : WordTrace (prefixWord ++ tailWord_1485518) baseStart_1485518 baseEnd_1485518 := by
    simpa [prefixWord, tailWord_1485518, baseEnd_1485518] using wordTrace_append hprefix tailTrace_1485518
  have hstable : (prefixWord ++ tailWord_1485518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485518).length < 2 ^ (prefixWord ++ tailWord_1485518).sum := by decide
  have hdescent : baseEnd_1485518 < baseStart_1485518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485528 : List Nat := [2, 1, 2, 2, 3, 3, 3, 7]
def baseStart_1485528 : Nat := 118140960795 + 1485528 * 2 ^ 59
def prefixEnd_1485528 : Nat := 4983230072969 + 3 ^ 40 * 1485528 * 2
def baseEnd_1485528 : Nat := 28251477396754411058081

theorem tailTrace_1485528 : CollatzResearch.WordTrace tailWord_1485528 prefixEnd_1485528 28251477396754411058081 := by
  unfold tailWord_1485528
  simp only [CollatzResearch.WordTrace]
  refine ⟨27090828681096619414392619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36121104908128825885856825 27090828681096619414392619)
  ·
    refine ⟨40636243021644929121588929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27090828681096619414392619 40636243021644929121588929)
    ·
      refine ⟨30477182266233696841191697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40636243021644929121588929 30477182266233696841191697)
      ·
        refine ⟨22857886699675272630893773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30477182266233696841191697 22857886699675272630893773)
        ·
          refine ⟨8571707512378227236585165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22857886699675272630893773 8571707512378227236585165)
          ·
            refine ⟨3214390317141835213719437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8571707512378227236585165 3214390317141835213719437)
            ·
              refine ⟨1205396368928188205144789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3214390317141835213719437 1205396368928188205144789)
              ·
                refine ⟨28251477396754411058081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1205396368928188205144789 28251477396754411058081)
                ·
                  rfl

theorem cell23_1485528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 7].length) (baseStart_1485528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1485528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1485528 prefixEnd_1485528 := by exact prefixLift 1485528
  have htrace : WordTrace (prefixWord ++ tailWord_1485528) baseStart_1485528 baseEnd_1485528 := by
    simpa [prefixWord, tailWord_1485528, baseEnd_1485528] using wordTrace_append hprefix tailTrace_1485528
  have hstable : (prefixWord ++ tailWord_1485528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485528).length < 2 ^ (prefixWord ++ tailWord_1485528).sum := by decide
  have hdescent : baseEnd_1485528 < baseStart_1485528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485539 : List Nat := [1, 1, 1, 7, 1, 1, 1, 5, 1, 2, 2]
def baseStart_1485539 : Nat := 118140960795 + 1485539 * 2 ^ 59
def prefixEnd_1485539 : Nat := 4983230072969 + 3 ^ 40 * 1485539 * 2
def baseEnd_1485539 : Nat := 762795537999568555530637

theorem tailTrace_1485539 : CollatzResearch.WordTrace tailWord_1485539 prefixEnd_1485539 762795537999568555530637 := by
  unfold tailWord_1485539
  simp only [CollatzResearch.WordTrace]
  refine ⟨54182058565153387707435671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36121372376768925138290447 54182058565153387707435671)
  ·
    refine ⟨81273087847730081561153507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54182058565153387707435671 81273087847730081561153507)
    ·
      refine ⟨121909631771595122341730261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81273087847730081561153507 121909631771595122341730261)
      ·
        refine ⟨2857256994646760679884303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 121909631771595122341730261 2857256994646760679884303)
        ·
          refine ⟨4285885491970141019826455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2857256994646760679884303 4285885491970141019826455)
          ·
            refine ⟨6428828237955211529739683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4285885491970141019826455 6428828237955211529739683)
            ·
              refine ⟨9643242356932817294609525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6428828237955211529739683 9643242356932817294609525)
              ·
                refine ⟨904053970962451621369643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9643242356932817294609525 904053970962451621369643)
                ·
                  refine ⟨1356080956443677432054465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 904053970962451621369643 1356080956443677432054465)
                  ·
                    refine ⟨1017060717332758074040849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1356080956443677432054465 1017060717332758074040849)
                    ·
                      refine ⟨762795537999568555530637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1017060717332758074040849 762795537999568555530637)
                      ·
                        rfl

theorem cell23_1485539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_1485539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1485539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1485539 prefixEnd_1485539 := by exact prefixLift 1485539
  have htrace : WordTrace (prefixWord ++ tailWord_1485539) baseStart_1485539 baseEnd_1485539 := by
    simpa [prefixWord, tailWord_1485539, baseEnd_1485539] using wordTrace_append hprefix tailTrace_1485539
  have hstable : (prefixWord ++ tailWord_1485539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485539).length < 2 ^ (prefixWord ++ tailWord_1485539).sum := by decide
  have hdescent : baseEnd_1485539 < baseStart_1485539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485561 : List Nat := [1, 2, 1, 3, 1, 1, 1, 3, 1, 5, 4]
def baseStart_1485561 : Nat := 118140960795 + 1485561 * 2 ^ 59
def prefixEnd_1485561 : Nat := 4983230072969 + 3 ^ 40 * 1485561 * 2
def baseEnd_1485561 : Nat := 762806834573967469455535

theorem tailTrace_1485561 : CollatzResearch.WordTrace tailWord_1485561 prefixEnd_1485561 762806834573967469455535 := by
  unfold tailWord_1485561
  simp only [CollatzResearch.WordTrace]
  refine ⟨54182860971073685464736537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36121907314049123643157691 54182860971073685464736537)
  ·
    refine ⟨40637145728305264098552403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54182860971073685464736537 40637145728305264098552403)
    ·
      refine ⟨60955718592457896147828605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40637145728305264098552403 60955718592457896147828605)
      ·
        refine ⟨22858394472171711055435727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60955718592457896147828605 22858394472171711055435727)
        ·
          refine ⟨34287591708257566583153591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22858394472171711055435727 34287591708257566583153591)
          ·
            refine ⟨51431387562386349874730387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34287591708257566583153591 51431387562386349874730387)
            ·
              refine ⟨77147081343579524812095581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51431387562386349874730387 77147081343579524812095581)
              ·
                refine ⟨28930155503842321804535843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77147081343579524812095581 28930155503842321804535843)
                ·
                  refine ⟨43395233255763482706803765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28930155503842321804535843 43395233255763482706803765)
                  ·
                    refine ⟨4068303117727826503762853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43395233255763482706803765 4068303117727826503762853)
                    ·
                      refine ⟨762806834573967469455535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4068303117727826503762853 762806834573967469455535)
                      ·
                        rfl

theorem cell23_1485561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_1485561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1485561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1485561 prefixEnd_1485561 := by exact prefixLift 1485561
  have htrace : WordTrace (prefixWord ++ tailWord_1485561) baseStart_1485561 baseEnd_1485561 := by
    simpa [prefixWord, tailWord_1485561, baseEnd_1485561] using wordTrace_append hprefix tailTrace_1485561
  have hstable : (prefixWord ++ tailWord_1485561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485561).length < 2 ^ (prefixWord ++ tailWord_1485561).sum := by decide
  have hdescent : baseEnd_1485561 < baseStart_1485561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485612 : List Nat := [2, 2, 1, 1, 1, 4, 2, 4, 2, 2, 2]
def baseStart_1485612 : Nat := 118140960795 + 1485612 * 2 ^ 59
def prefixEnd_1485612 : Nat := 4983230072969 + 3 ^ 40 * 1485612 * 2
def baseEnd_1485612 : Nat := 762833022087346769917801

theorem tailTrace_1485612 : CollatzResearch.WordTrace tailWord_1485612 prefixEnd_1485612 762833022087346769917801 := by
  unfold tailWord_1485612
  simp only [CollatzResearch.WordTrace]
  refine ⟨27092360546944460587421545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36123147395925947449895393 27092360546944460587421545)
  ·
    refine ⟨20319270410208345440566159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27092360546944460587421545 20319270410208345440566159)
    ·
      refine ⟨30478905615312518160849239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20319270410208345440566159 30478905615312518160849239)
      ·
        refine ⟨45718358422968777241273859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30478905615312518160849239 45718358422968777241273859)
        ·
          refine ⟨68577537634453165861910789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45718358422968777241273859 68577537634453165861910789)
          ·
            refine ⟨12858288306459968599108273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68577537634453165861910789 12858288306459968599108273)
            ·
              refine ⟨9643716229844976449331205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12858288306459968599108273 9643716229844976449331205)
              ·
                refine ⟨1808196793095933084249601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9643716229844976449331205 1808196793095933084249601)
                ·
                  refine ⟨1356147594821949813187201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1808196793095933084249601 1356147594821949813187201)
                  ·
                    refine ⟨1017110696116462359890401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1356147594821949813187201 1017110696116462359890401)
                    ·
                      refine ⟨762833022087346769917801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1017110696116462359890401 762833022087346769917801)
                      ·
                        rfl

theorem cell23_1485612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 2, 2].length) (baseStart_1485612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1485612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1485612 prefixEnd_1485612 := by exact prefixLift 1485612
  have htrace : WordTrace (prefixWord ++ tailWord_1485612) baseStart_1485612 baseEnd_1485612 := by
    simpa [prefixWord, tailWord_1485612, baseEnd_1485612] using wordTrace_append hprefix tailTrace_1485612
  have hstable : (prefixWord ++ tailWord_1485612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485612).length < 2 ^ (prefixWord ++ tailWord_1485612).sum := by decide
  have hdescent : baseEnd_1485612 < baseStart_1485612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485628 : List Nat := [2, 2, 2, 2, 1, 1, 1, 3, 1, 5, 3]
def baseStart_1485628 : Nat := 118140960795 + 1485628 * 2 ^ 59
def prefixEnd_1485628 : Nat := 4983230072969 + 3 ^ 40 * 1485628 * 2
def baseEnd_1485628 : Nat := 762841237777818707317727

theorem tailTrace_1485628 : CollatzResearch.WordTrace tailWord_1485628 prefixEnd_1485628 762841237777818707317727 := by
  unfold tailWord_1485628
  simp only [CollatzResearch.WordTrace]
  refine ⟨27092652330915477953712769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36123536441220637271617025 27092652330915477953712769)
  ·
    refine ⟨20319489248186608465284577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27092652330915477953712769 20319489248186608465284577)
    ·
      refine ⟨15239616936139956348963433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20319489248186608465284577 15239616936139956348963433)
      ·
        refine ⟨11429712702104967261722575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15239616936139956348963433 11429712702104967261722575)
        ·
          refine ⟨17144569053157450892583863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11429712702104967261722575 17144569053157450892583863)
          ·
            refine ⟨25716853579736176338875795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17144569053157450892583863 25716853579736176338875795)
            ·
              refine ⟨38575280369604264508313693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25716853579736176338875795 38575280369604264508313693)
              ·
                refine ⟨14465730138601599190617635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38575280369604264508313693 14465730138601599190617635)
                ·
                  refine ⟨21698595207902398785926453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14465730138601599190617635 21698595207902398785926453)
                  ·
                    refine ⟨2034243300740849886180605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21698595207902398785926453 2034243300740849886180605)
                    ·
                      refine ⟨762841237777818707317727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2034243300740849886180605 762841237777818707317727)
                      ·
                        rfl

theorem cell23_1485628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_1485628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1485628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1485628 prefixEnd_1485628 := by exact prefixLift 1485628
  have htrace : WordTrace (prefixWord ++ tailWord_1485628) baseStart_1485628 baseEnd_1485628 := by
    simpa [prefixWord, tailWord_1485628, baseEnd_1485628] using wordTrace_append hprefix tailTrace_1485628
  have hstable : (prefixWord ++ tailWord_1485628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485628).length < 2 ^ (prefixWord ++ tailWord_1485628).sum := by decide
  have hdescent : baseEnd_1485628 < baseStart_1485628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485633 : List Nat := [1, 2, 5, 3, 2, 1, 1, 2, 1, 3, 2]
def baseStart_1485633 : Nat := 118140960795 + 1485633 * 2 ^ 59
def prefixEnd_1485633 : Nat := 4983230072969 + 3 ^ 40 * 1485633 * 2
def baseEnd_1485633 : Nat := 762843805181091187755205

theorem tailTrace_1485633 : CollatzResearch.WordTrace tailWord_1485633 prefixEnd_1485633 762843805181091187755205 := by
  unfold tailWord_1485633
  simp only [CollatzResearch.WordTrace]
  refine ⟨54185487026812841761357553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36123658017875227840905035 54185487026812841761357553)
  ·
    refine ⟨40639115270109631321018165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54185487026812841761357553 40639115270109631321018165)
    ·
      refine ⟨3809917056572777936345453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40639115270109631321018165 3809917056572777936345453)
      ·
        refine ⟨1428718896214791726129545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3809917056572777936345453 1428718896214791726129545)
        ·
          refine ⟨1071539172161093794597159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1428718896214791726129545 1071539172161093794597159)
          ·
            refine ⟨1607308758241640691895739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1071539172161093794597159 1607308758241640691895739)
            ·
              refine ⟨2410963137362461037843609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1607308758241640691895739 2410963137362461037843609)
              ·
                refine ⟨1808222353021845778382707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2410963137362461037843609 1808222353021845778382707)
                ·
                  refine ⟨2712333529532768667574061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1808222353021845778382707 2712333529532768667574061)
                  ·
                    refine ⟨1017125073574788250340273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2712333529532768667574061 1017125073574788250340273)
                    ·
                      refine ⟨762843805181091187755205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1017125073574788250340273 762843805181091187755205)
                      ·
                        rfl

theorem cell23_1485633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_1485633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1485633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1485633 prefixEnd_1485633 := by exact prefixLift 1485633
  have htrace : WordTrace (prefixWord ++ tailWord_1485633) baseStart_1485633 baseEnd_1485633 := by
    simpa [prefixWord, tailWord_1485633, baseEnd_1485633] using wordTrace_append hprefix tailTrace_1485633
  have hstable : (prefixWord ++ tailWord_1485633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485633).length < 2 ^ (prefixWord ++ tailWord_1485633).sum := by decide
  have hdescent : baseEnd_1485633 < baseStart_1485633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485648 : List Nat := [2, 1, 1, 1, 1, 4, 3, 3, 2, 5]
def baseStart_1485648 : Nat := 118140960795 + 1485648 * 2 ^ 59
def prefixEnd_1485648 : Nat := 4983230072969 + 3 ^ 40 * 1485648 * 2
def baseEnd_1485648 : Nat := 254283835796969543022545

theorem tailTrace_1485648 : CollatzResearch.WordTrace tailWord_1485648 prefixEnd_1485648 254283835796969543022545 := by
  unfold tailWord_1485648
  simp only [CollatzResearch.WordTrace]
  refine ⟨27093017060879249661576799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36124022747838999548769065 27093017060879249661576799)
  ·
    refine ⟨40639525591318874492365199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27093017060879249661576799 40639525591318874492365199)
    ·
      refine ⟨60959288386978311738547799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40639525591318874492365199 60959288386978311738547799)
      ·
        refine ⟨91438932580467467607821699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60959288386978311738547799 91438932580467467607821699)
        ·
          refine ⟨137158398870701201411732549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91438932580467467607821699 137158398870701201411732549)
          ·
            refine ⟨25717199788256475264699853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137158398870701201411732549 25717199788256475264699853)
            ·
              refine ⟨9643949920596178224262445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25717199788256475264699853 9643949920596178224262445)
              ·
                refine ⟨3616481220223566834098417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9643949920596178224262445 3616481220223566834098417)
                ·
                  refine ⟨2712360915167675125573813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3616481220223566834098417 2712360915167675125573813)
                  ·
                    refine ⟨254283835796969543022545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2712360915167675125573813 254283835796969543022545)
                    ·
                      rfl

theorem cell23_1485648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3, 2, 5].length) (baseStart_1485648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1485648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1485648 prefixEnd_1485648 := by exact prefixLift 1485648
  have htrace : WordTrace (prefixWord ++ tailWord_1485648) baseStart_1485648 baseEnd_1485648 := by
    simpa [prefixWord, tailWord_1485648, baseEnd_1485648] using wordTrace_append hprefix tailTrace_1485648
  have hstable : (prefixWord ++ tailWord_1485648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485648).length < 2 ^ (prefixWord ++ tailWord_1485648).sum := by decide
  have hdescent : baseEnd_1485648 < baseStart_1485648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485658 : List Nat := [3, 1, 1, 2, 1, 4, 1, 2, 1, 2, 5]
def baseStart_1485658 : Nat := 118140960795 + 1485658 * 2 ^ 59
def prefixEnd_1485658 : Nat := 4983230072969 + 3 ^ 40 * 1485658 * 2
def baseEnd_1485658 : Nat := 762856642197453589942589

theorem tailTrace_1485658 : CollatzResearch.WordTrace tailWord_1485658 prefixEnd_1485658 762856642197453589942589 := by
  unfold tailWord_1485658
  simp only [CollatzResearch.WordTrace]
  refine ⟨13546599712930567757754407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36124265901148180687345085 13546599712930567757754407)
  ·
    refine ⟨20319899569395851636631611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13546599712930567757754407 20319899569395851636631611)
    ·
      refine ⟨30479849354093777454947417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20319899569395851636631611 30479849354093777454947417)
      ·
        refine ⟨22859887015570333091210563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30479849354093777454947417 22859887015570333091210563)
        ·
          refine ⟨34289830523355499636815845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22859887015570333091210563 34289830523355499636815845)
          ·
            refine ⟨6429343223129156181902971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34289830523355499636815845 6429343223129156181902971)
            ·
              refine ⟨9644014834693734272854457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6429343223129156181902971 9644014834693734272854457)
              ·
                refine ⟨7233011126020300704640843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9644014834693734272854457 7233011126020300704640843)
                ·
                  refine ⟨10849516689030451056961265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7233011126020300704640843 10849516689030451056961265)
                  ·
                    refine ⟨8137137516772838292720949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10849516689030451056961265 8137137516772838292720949)
                    ·
                      refine ⟨762856642197453589942589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8137137516772838292720949 762856642197453589942589)
                      ·
                        rfl

theorem cell23_1485658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_1485658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1485658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1485658 prefixEnd_1485658 := by exact prefixLift 1485658
  have htrace : WordTrace (prefixWord ++ tailWord_1485658) baseStart_1485658 baseEnd_1485658 := by
    simpa [prefixWord, tailWord_1485658, baseEnd_1485658] using wordTrace_append hprefix tailTrace_1485658
  have hstable : (prefixWord ++ tailWord_1485658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485658).length < 2 ^ (prefixWord ++ tailWord_1485658).sum := by decide
  have hdescent : baseEnd_1485658 < baseStart_1485658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485705 : List Nat := [1, 2, 1, 1, 5, 3, 1, 1, 1, 4, 3]
def baseStart_1485705 : Nat := 118140960795 + 1485705 * 2 ^ 59
def prefixEnd_1485705 : Nat := 4983230072969 + 3 ^ 40 * 1485705 * 2
def baseEnd_1485705 : Nat := 762880775788214906054873

theorem tailTrace_1485705 : CollatzResearch.WordTrace tailWord_1485705 prefixEnd_1485705 762880775788214906054873 := by
  unfold tailWord_1485705
  simp only [CollatzResearch.WordTrace]
  refine ⟨54188113082551998057978569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36125408721701332038652379 54188113082551998057978569)
  ·
    refine ⟨40641084811913998543483927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54188113082551998057978569 40641084811913998543483927)
    ·
      refine ⟨60961627217870997815225891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40641084811913998543483927 60961627217870997815225891)
      ·
        refine ⟨91442440826806496722838837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60961627217870997815225891 91442440826806496722838837)
        ·
          refine ⟨8572728827513109067766141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 91442440826806496722838837 8572728827513109067766141)
          ·
            refine ⟨3214773310317415900412303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8572728827513109067766141 3214773310317415900412303)
            ·
              refine ⟨4822159965476123850618455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3214773310317415900412303 4822159965476123850618455)
              ·
                refine ⟨7233239948214185775927683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4822159965476123850618455 7233239948214185775927683)
                ·
                  refine ⟨10849859922321278663891525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7233239948214185775927683 10849859922321278663891525)
                  ·
                    refine ⟨2034348735435239749479661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10849859922321278663891525 2034348735435239749479661)
                    ·
                      refine ⟨762880775788214906054873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2034348735435239749479661 762880775788214906054873)
                      ·
                        rfl

theorem cell23_1485705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 4, 3].length) (baseStart_1485705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1485705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1485705 prefixEnd_1485705 := by exact prefixLift 1485705
  have htrace : WordTrace (prefixWord ++ tailWord_1485705) baseStart_1485705 baseEnd_1485705 := by
    simpa [prefixWord, tailWord_1485705, baseEnd_1485705] using wordTrace_append hprefix tailTrace_1485705
  have hstable : (prefixWord ++ tailWord_1485705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485705).length < 2 ^ (prefixWord ++ tailWord_1485705).sum := by decide
  have hdescent : baseEnd_1485705 < baseStart_1485705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485728 : List Nat := [2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 6]
def baseStart_1485728 : Nat := 118140960795 + 1485728 * 2 ^ 59
def prefixEnd_1485728 : Nat := 4983230072969 + 3 ^ 40 * 1485728 * 2
def baseEnd_1485728 : Nat := 762892585843268316067267

theorem tailTrace_1485728 : CollatzResearch.WordTrace tailWord_1485728 prefixEnd_1485728 762892585843268316067267 := by
  unfold tailWord_1485728
  simp only [CollatzResearch.WordTrace]
  refine ⟨27094475980734336493032919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36125967974312448657377225 27094475980734336493032919)
  ·
    refine ⟨40641713971101504739549379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27094475980734336493032919 40641713971101504739549379)
    ·
      refine ⟨60962570956652257109324069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40641713971101504739549379 60962570956652257109324069)
      ·
        refine ⟨11430482054372298207998263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60962570956652257109324069 11430482054372298207998263)
        ·
          refine ⟨17145723081558447311997395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11430482054372298207998263 17145723081558447311997395)
          ·
            refine ⟨25718584622337670967996093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17145723081558447311997395 25718584622337670967996093)
            ·
              refine ⟨9644469233376626612998535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25718584622337670967996093 9644469233376626612998535)
              ·
                refine ⟨14466703850064939919497803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9644469233376626612998535 14466703850064939919497803)
                ·
                  refine ⟨21700055775097409879246705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14466703850064939919497803 21700055775097409879246705)
                  ·
                    refine ⟨16275041831323057409435029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21700055775097409879246705 16275041831323057409435029)
                    ·
                      refine ⟨762892585843268316067267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16275041831323057409435029 762892585843268316067267)
                      ·
                        rfl

theorem cell23_1485728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_1485728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1485728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1485728 prefixEnd_1485728 := by exact prefixLift 1485728
  have htrace : WordTrace (prefixWord ++ tailWord_1485728) baseStart_1485728 baseEnd_1485728 := by
    simpa [prefixWord, tailWord_1485728, baseEnd_1485728] using wordTrace_append hprefix tailTrace_1485728
  have hstable : (prefixWord ++ tailWord_1485728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485728).length < 2 ^ (prefixWord ++ tailWord_1485728).sum := by decide
  have hdescent : baseEnd_1485728 < baseStart_1485728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485729 : List Nat := [1, 2, 3, 4, 1, 1, 2, 4, 1, 4]
def baseStart_1485729 : Nat := 118140960795 + 1485729 * 2 ^ 59
def prefixEnd_1485729 : Nat := 4983230072969 + 3 ^ 40 * 1485729 * 2
def baseEnd_1485729 : Nat := 254297699774640937384921

theorem tailTrace_1485729 : CollatzResearch.WordTrace tailWord_1485729 prefixEnd_1485729 254297699774640937384921 := by
  unfold tailWord_1485729
  simp only [CollatzResearch.WordTrace]
  refine ⟨54188988434465050156852241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36125992289643366771234827 54188988434465050156852241)
  ·
    refine ⟨40641741325848787617639181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54188988434465050156852241 40641741325848787617639181)
    ·
      refine ⟨15240652997193295356614693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40641741325848787617639181 15240652997193295356614693)
      ·
        refine ⟨2857622436973742879365255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15240652997193295356614693 2857622436973742879365255)
        ·
          refine ⟨4286433655460614319047883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2857622436973742879365255 4286433655460614319047883)
          ·
            refine ⟨6429650483190921478571825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4286433655460614319047883 6429650483190921478571825)
            ·
              refine ⟨4822237862393191108928869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6429650483190921478571825 4822237862393191108928869)
              ·
                refine ⟨904169599198723332924163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4822237862393191108928869 904169599198723332924163)
                ·
                  refine ⟨1356254398798084999386245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 904169599198723332924163 1356254398798084999386245)
                  ·
                    refine ⟨254297699774640937384921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1356254398798084999386245 254297699774640937384921)
                    ·
                      rfl

theorem cell23_1485729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 4, 1, 4].length) (baseStart_1485729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1485729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1485729 prefixEnd_1485729 := by exact prefixLift 1485729
  have htrace : WordTrace (prefixWord ++ tailWord_1485729) baseStart_1485729 baseEnd_1485729 := by
    simpa [prefixWord, tailWord_1485729, baseEnd_1485729] using wordTrace_append hprefix tailTrace_1485729
  have hstable : (prefixWord ++ tailWord_1485729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485729).length < 2 ^ (prefixWord ++ tailWord_1485729).sum := by decide
  have hdescent : baseEnd_1485729 < baseStart_1485729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485752 : List Nat := [2, 1, 2, 1, 2, 4, 2, 2, 3, 1, 3]
def baseStart_1485752 : Nat := 118140960795 + 1485752 * 2 ^ 59
def prefixEnd_1485752 : Nat := 4983230072969 + 3 ^ 40 * 1485752 * 2
def baseEnd_1485752 : Nat := 762904909378976222167157

theorem tailTrace_1485752 : CollatzResearch.WordTrace tailWord_1485752 prefixEnd_1485752 762904909378976222167157 := by
  unfold tailWord_1485752
  simp only [CollatzResearch.WordTrace]
  refine ⟨27094913656690862542469755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36126551542254483389959673 27094913656690862542469755)
  ·
    refine ⟨40642370485036293813704633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27094913656690862542469755 40642370485036293813704633)
    ·
      refine ⟨30481777863777220360278475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40642370485036293813704633 30481777863777220360278475)
      ·
        refine ⟨45722666795665830540417713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30481777863777220360278475 45722666795665830540417713)
        ·
          refine ⟨34292000096749372905313285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45722666795665830540417713 34292000096749372905313285)
          ·
            refine ⟨6429750018140507419746241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34292000096749372905313285 6429750018140507419746241)
            ·
              refine ⟨4822312513605380564809681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6429750018140507419746241 4822312513605380564809681)
              ·
                refine ⟨3616734385204035423607261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4822312513605380564809681 3616734385204035423607261)
                ·
                  refine ⟨1356275394451513283852723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3616734385204035423607261 1356275394451513283852723)
                  ·
                    refine ⟨2034413091677269925779085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1356275394451513283852723 2034413091677269925779085)
                    ·
                      refine ⟨762904909378976222167157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2034413091677269925779085 762904909378976222167157)
                      ·
                        rfl

theorem cell23_1485752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2, 3, 1, 3].length) (baseStart_1485752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1485752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1485752 prefixEnd_1485752 := by exact prefixLift 1485752
  have htrace : WordTrace (prefixWord ++ tailWord_1485752) baseStart_1485752 baseEnd_1485752 := by
    simpa [prefixWord, tailWord_1485752, baseEnd_1485752] using wordTrace_append hprefix tailTrace_1485752
  have hstable : (prefixWord ++ tailWord_1485752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485752).length < 2 ^ (prefixWord ++ tailWord_1485752).sum := by decide
  have hdescent : baseEnd_1485752 < baseStart_1485752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485773 : List Nat := [1, 6, 3, 1, 1, 1, 1, 2, 2, 2, 3]
def baseStart_1485773 : Nat := 118140960795 + 1485773 * 2 ^ 59
def prefixEnd_1485773 : Nat := 4983230072969 + 3 ^ 40 * 1485773 * 2
def baseEnd_1485773 : Nat := 762915692472720640004561

theorem tailTrace_1485773 : CollatzResearch.WordTrace tailWord_1485773 prefixEnd_1485773 762915692472720640004561 := by
  unfold tailWord_1485773
  simp only [CollatzResearch.WordTrace]
  refine ⟨54190593246305645671453973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36127062164203763780969315 54190593246305645671453973)
  ·
    refine ⟨2540184058420577140849405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 54190593246305645671453973 2540184058420577140849405)
    ·
      refine ⟨952569021907716427818527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2540184058420577140849405 952569021907716427818527)
      ·
        refine ⟨1428853532861574641727791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 952569021907716427818527 1428853532861574641727791)
        ·
          refine ⟨2143280299292361962591687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1428853532861574641727791 2143280299292361962591687)
          ·
            refine ⟨3214920448938542943887531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2143280299292361962591687 3214920448938542943887531)
            ·
              refine ⟨4822380673407814415831297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3214920448938542943887531 4822380673407814415831297)
              ·
                refine ⟨3616785505055860811873473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4822380673407814415831297 3616785505055860811873473)
                ·
                  refine ⟨2712589128791895608905105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3616785505055860811873473 2712589128791895608905105)
                  ·
                    refine ⟨2034441846593921706678829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2712589128791895608905105 2034441846593921706678829)
                    ·
                      refine ⟨762915692472720640004561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2034441846593921706678829 762915692472720640004561)
                      ·
                        rfl

theorem cell23_1485773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_1485773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1485773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1485773 prefixEnd_1485773 := by exact prefixLift 1485773
  have htrace : WordTrace (prefixWord ++ tailWord_1485773) baseStart_1485773 baseEnd_1485773 := by
    simpa [prefixWord, tailWord_1485773, baseEnd_1485773] using wordTrace_append hprefix tailTrace_1485773
  have hstable : (prefixWord ++ tailWord_1485773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485773).length < 2 ^ (prefixWord ++ tailWord_1485773).sum := by decide
  have hdescent : baseEnd_1485773 < baseStart_1485773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485795 : List Nat := [1, 1, 1, 6, 1, 1, 1, 4, 1, 1, 5]
def baseStart_1485795 : Nat := 118140960795 + 1485795 * 2 ^ 59
def prefixEnd_1485795 : Nat := 4983230072969 + 3 ^ 40 * 1485795 * 2
def baseEnd_1485795 : Nat := 762926989047119553929459

theorem tailTrace_1485795 : CollatzResearch.WordTrace tailWord_1485795 prefixEnd_1485795 762926989047119553929459 := by
  unfold tailWord_1485795
  simp only [CollatzResearch.WordTrace]
  refine ⟨54191395652225943428754839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36127597101483962285836559 54191395652225943428754839)
  ·
    refine ⟨81287093478338915143132259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54191395652225943428754839 81287093478338915143132259)
    ·
      refine ⟨121930640217508372714698389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81287093478338915143132259 121930640217508372714698389)
      ·
        refine ⟨5715498760195704971001487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 121930640217508372714698389 5715498760195704971001487)
        ·
          refine ⟨8573248140293557456502231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5715498760195704971001487 8573248140293557456502231)
          ·
            refine ⟨12859872210440336184753347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8573248140293557456502231 12859872210440336184753347)
            ·
              refine ⟨19289808315660504277130021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12859872210440336184753347 19289808315660504277130021)
              ·
                refine ⟨3616839059186344551961879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19289808315660504277130021 3616839059186344551961879)
                ·
                  refine ⟨5425258588779516827942819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3616839059186344551961879 5425258588779516827942819)
                  ·
                    refine ⟨8137887883169275241914229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5425258588779516827942819 8137887883169275241914229)
                    ·
                      refine ⟨762926989047119553929459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8137887883169275241914229 762926989047119553929459)
                      ·
                        rfl

theorem cell23_1485795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_1485795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1485795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1485795 prefixEnd_1485795 := by exact prefixLift 1485795
  have htrace : WordTrace (prefixWord ++ tailWord_1485795) baseStart_1485795 baseEnd_1485795 := by
    simpa [prefixWord, tailWord_1485795, baseEnd_1485795] using wordTrace_append hprefix tailTrace_1485795
  have hstable : (prefixWord ++ tailWord_1485795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485795).length < 2 ^ (prefixWord ++ tailWord_1485795).sum := by decide
  have hdescent : baseEnd_1485795 < baseStart_1485795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485806 : List Nat := [4, 1, 2, 1, 5, 1, 1, 2, 1, 5]
def baseStart_1485806 : Nat := 118140960795 + 1485806 * 2 ^ 59
def prefixEnd_1485806 : Nat := 4983230072969 + 3 ^ 40 * 1485806 * 2
def baseEnd_1485806 : Nat := 254310879111439670297303

theorem tailTrace_1485806 : CollatzResearch.WordTrace tailWord_1485806 prefixEnd_1485806 254310879111439670297303 := by
  unfold tailWord_1485806
  simp only [CollatzResearch.WordTrace]
  refine ⟨6773974606898261538425659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36127864570124061538270181 6773974606898261538425659)
  ·
    refine ⟨10160961910347392307638489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6773974606898261538425659 10160961910347392307638489)
    ·
      refine ⟨7620721432760544230728867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10160961910347392307638489 7620721432760544230728867)
      ·
        refine ⟨11431082149140816346093301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7620721432760544230728867 11431082149140816346093301)
        ·
          refine ⟨1071663951481951532446247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11431082149140816346093301 1071663951481951532446247)
          ·
            refine ⟨1607495927222927298669371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1071663951481951532446247 1607495927222927298669371)
            ·
              refine ⟨2411243890834390948004057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1607495927222927298669371 2411243890834390948004057)
              ·
                refine ⟨1808432918125793211003043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2411243890834390948004057 1808432918125793211003043)
                ·
                  refine ⟨2712649377188689816504565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1808432918125793211003043 2712649377188689816504565)
                  ·
                    refine ⟨254310879111439670297303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2712649377188689816504565 254310879111439670297303)
                    ·
                      rfl

theorem cell23_1485806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 2, 1, 5].length) (baseStart_1485806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1485806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1485806 prefixEnd_1485806 := by exact prefixLift 1485806
  have htrace : WordTrace (prefixWord ++ tailWord_1485806) baseStart_1485806 baseEnd_1485806 := by
    simpa [prefixWord, tailWord_1485806, baseEnd_1485806] using wordTrace_append hprefix tailTrace_1485806
  have hstable : (prefixWord ++ tailWord_1485806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485806).length < 2 ^ (prefixWord ++ tailWord_1485806).sum := by decide
  have hdescent : baseEnd_1485806 < baseStart_1485806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485809 : List Nat := [1, 2, 2, 2, 4, 3, 1, 2, 1, 1, 4]
def baseStart_1485809 : Nat := 118140960795 + 1485809 * 2 ^ 59
def prefixEnd_1485809 : Nat := 4983230072969 + 3 ^ 40 * 1485809 * 2
def baseEnd_1485809 : Nat := 762934177776282499154395

theorem tailTrace_1485809 : CollatzResearch.WordTrace tailWord_1485809 prefixEnd_1485809 762934177776282499154395 := by
  unfold tailWord_1485809
  simp only [CollatzResearch.WordTrace]
  refine ⟨54191906274175223819764481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36127937516116815879842987 54191906274175223819764481)
  ·
    refine ⟨40643929705631417864823361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54191906274175223819764481 40643929705631417864823361)
    ·
      refine ⟨30482947279223563398617521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40643929705631417864823361 30482947279223563398617521)
      ·
        refine ⟨22862210459417672548963141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30482947279223563398617521 22862210459417672548963141)
        ·
          refine ⟨4286664461140813602930589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22862210459417672548963141 4286664461140813602930589)
          ·
            refine ⟨1607499172927805101098971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4286664461140813602930589 1607499172927805101098971)
            ·
              refine ⟨2411248759391707651648457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1607499172927805101098971 2411248759391707651648457)
              ·
                refine ⟨1808436569543780738736343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2411248759391707651648457 1808436569543780738736343)
                ·
                  refine ⟨2712654854315671108104515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1808436569543780738736343 2712654854315671108104515)
                  ·
                    refine ⟨4068982281473506662156773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2712654854315671108104515 4068982281473506662156773)
                    ·
                      refine ⟨762934177776282499154395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4068982281473506662156773 762934177776282499154395)
                      ·
                        rfl

theorem cell23_1485809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 2, 1, 1, 4].length) (baseStart_1485809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1485809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1485809 prefixEnd_1485809 := by exact prefixLift 1485809
  have htrace : WordTrace (prefixWord ++ tailWord_1485809) baseStart_1485809 baseEnd_1485809 := by
    simpa [prefixWord, tailWord_1485809, baseEnd_1485809] using wordTrace_append hprefix tailTrace_1485809
  have hstable : (prefixWord ++ tailWord_1485809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485809).length < 2 ^ (prefixWord ++ tailWord_1485809).sum := by decide
  have hdescent : baseEnd_1485809 < baseStart_1485809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485813 : List Nat := [1, 3, 5, 2, 1, 1, 2, 1, 2, 3, 2]
def baseStart_1485813 : Nat := 118140960795 + 1485813 * 2 ^ 59
def prefixEnd_1485813 : Nat := 4983230072969 + 3 ^ 40 * 1485813 * 2
def baseEnd_1485813 : Nat := 762936231698900483504377

theorem tailTrace_1485813 : CollatzResearch.WordTrace tailWord_1485813 prefixEnd_1485813 762936231698900483504377 := by
  unfold tailWord_1485813
  simp only [CollatzResearch.WordTrace]
  refine ⟨54192052166160732502910093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36128034777440488335273395 54192052166160732502910093)
  ·
    refine ⟨20322019562310274688591285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54192052166160732502910093 20322019562310274688591285)
    ·
      refine ⟨1905189333966588252055433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20322019562310274688591285 1905189333966588252055433)
      ·
        refine ⟨1428892000474941189041575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1905189333966588252055433 1428892000474941189041575)
        ·
          refine ⟨2143338000712411783562363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1428892000474941189041575 2143338000712411783562363)
          ·
            refine ⟨3215007001068617675343545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2143338000712411783562363 3215007001068617675343545)
            ·
              refine ⟨2411255250801463256507659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3215007001068617675343545 2411255250801463256507659)
              ·
                refine ⟨3616882876202194884761489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2411255250801463256507659 3616882876202194884761489)
                ·
                  refine ⟨2712662157151646163571117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3616882876202194884761489 2712662157151646163571117)
                  ·
                    refine ⟨1017248308931867311339169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2712662157151646163571117 1017248308931867311339169)
                    ·
                      refine ⟨762936231698900483504377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1017248308931867311339169 762936231698900483504377)
                      ·
                        rfl

theorem cell23_1485813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_1485813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1485813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1485813 prefixEnd_1485813 := by exact prefixLift 1485813
  have htrace : WordTrace (prefixWord ++ tailWord_1485813) baseStart_1485813 baseEnd_1485813 := by
    simpa [prefixWord, tailWord_1485813, baseEnd_1485813] using wordTrace_append hprefix tailTrace_1485813
  have hstable : (prefixWord ++ tailWord_1485813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485813).length < 2 ^ (prefixWord ++ tailWord_1485813).sum := by decide
  have hdescent : baseEnd_1485813 < baseStart_1485813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485829 : List Nat := [1, 3, 1, 1, 2, 3, 5, 1, 1, 2, 3]
def baseStart_1485829 : Nat := 118140960795 + 1485829 * 2 ^ 59
def prefixEnd_1485829 : Nat := 4983230072969 + 3 ^ 40 * 1485829 * 2
def baseEnd_1485829 : Nat := 762944447389372420904303

theorem tailTrace_1485829 : CollatzResearch.WordTrace tailWord_1485829 prefixEnd_1485829 762944447389372420904303 := by
  unfold tailWord_1485829
  simp only [CollatzResearch.WordTrace]
  refine ⟨54192635734102767235492541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36128423822735178156995027 54192635734102767235492541)
  ·
    refine ⟨20322238400288537713309703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54192635734102767235492541 20322238400288537713309703)
    ·
      refine ⟨30483357600432806569964555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20322238400288537713309703 30483357600432806569964555)
      ·
        refine ⟨45725036400649209854946833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30483357600432806569964555 45725036400649209854946833)
        ·
          refine ⟨34293777300486907391210125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45725036400649209854946833 34293777300486907391210125)
          ·
            refine ⟨12860166487682590271703797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34293777300486907391210125 12860166487682590271703797)
            ·
              refine ⟨1205640608220242837972231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12860166487682590271703797 1205640608220242837972231)
              ·
                refine ⟨1808460912330364256958347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1205640608220242837972231 1808460912330364256958347)
                ·
                  refine ⟨2712691368495546385437521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1808460912330364256958347 2712691368495546385437521)
                  ·
                    refine ⟨2034518526371659789078141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2712691368495546385437521 2034518526371659789078141)
                    ·
                      refine ⟨762944447389372420904303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2034518526371659789078141 762944447389372420904303)
                      ·
                        rfl

theorem cell23_1485829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 1, 1, 2, 3].length) (baseStart_1485829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1485829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1485829 prefixEnd_1485829 := by exact prefixLift 1485829
  have htrace : WordTrace (prefixWord ++ tailWord_1485829) baseStart_1485829 baseEnd_1485829 := by
    simpa [prefixWord, tailWord_1485829, baseEnd_1485829] using wordTrace_append hprefix tailTrace_1485829
  have hstable : (prefixWord ++ tailWord_1485829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485829).length < 2 ^ (prefixWord ++ tailWord_1485829).sum := by decide
  have hdescent : baseEnd_1485829 < baseStart_1485829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485845 : List Nat := [1, 3, 2, 1, 4, 1, 1, 1, 2, 7]
def baseStart_1485845 : Nat := 118140960795 + 1485845 * 2 ^ 59
def prefixEnd_1485845 : Nat := 4983230072969 + 3 ^ 40 * 1485845 * 2
def baseEnd_1485845 : Nat := 254317554359948119434743

theorem tailTrace_1485845 : CollatzResearch.WordTrace tailWord_1485845 prefixEnd_1485845 254317554359948119434743 := by
  unfold tailWord_1485845
  simp only [CollatzResearch.WordTrace]
  refine ⟨54193219302044801968074989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36128812868029867978716659 54193219302044801968074989)
  ·
    refine ⟨20322457238266800738028121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54193219302044801968074989 20322457238266800738028121)
    ·
      refine ⟨15241842928700100553521091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20322457238266800738028121 15241842928700100553521091)
      ·
        refine ⟨22862764393050150830281637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15241842928700100553521091 22862764393050150830281637)
        ·
          refine ⟨4286768323696903280677807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22862764393050150830281637 4286768323696903280677807)
          ·
            refine ⟨6430152485545354921016711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4286768323696903280677807 6430152485545354921016711)
            ·
              refine ⟨9645228728318032381525067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6430152485545354921016711 9645228728318032381525067)
              ·
                refine ⟨14467843092477048572287601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9645228728318032381525067 14467843092477048572287601)
                ·
                  refine ⟨10850882319357786429215701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14467843092477048572287601 10850882319357786429215701)
                  ·
                    refine ⟨254317554359948119434743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10850882319357786429215701 254317554359948119434743)
                    ·
                      rfl

theorem cell23_1485845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 7].length) (baseStart_1485845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1485845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1485845 prefixEnd_1485845 := by exact prefixLift 1485845
  have htrace : WordTrace (prefixWord ++ tailWord_1485845) baseStart_1485845 baseEnd_1485845 := by
    simpa [prefixWord, tailWord_1485845, baseEnd_1485845] using wordTrace_append hprefix tailTrace_1485845
  have hstable : (prefixWord ++ tailWord_1485845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485845).length < 2 ^ (prefixWord ++ tailWord_1485845).sum := by decide
  have hdescent : baseEnd_1485845 < baseStart_1485845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485859 : List Nat := [1, 1, 1, 4, 3, 2, 2, 3, 2, 1, 3]
def baseStart_1485859 : Nat := 118140960795 + 1485859 * 2 ^ 59
def prefixEnd_1485859 : Nat := 4983230072969 + 3 ^ 40 * 1485859 * 2
def baseEnd_1485859 : Nat := 762959851809007303529165

theorem tailTrace_1485859 : CollatzResearch.WordTrace tailWord_1485859 prefixEnd_1485859 762959851809007303529165 := by
  unfold tailWord_1485859
  simp only [CollatzResearch.WordTrace]
  refine ⟨54193729923994082359084631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36129153282662721572723087 54193729923994082359084631)
  ·
    refine ⟨81290594885991123538626947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54193729923994082359084631 81290594885991123538626947)
    ·
      refine ⟨121935892328986685307940421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81290594885991123538626947 121935892328986685307940421)
      ·
        refine ⟨22862979811685003495238829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121935892328986685307940421 22862979811685003495238829)
        ·
          refine ⟨8573617429381876310714561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22862979811685003495238829 8573617429381876310714561)
          ·
            refine ⟨6430213072036407233035921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8573617429381876310714561 6430213072036407233035921)
            ·
              refine ⟨4822659804027305424776941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6430213072036407233035921 4822659804027305424776941)
              ·
                refine ⟨1808497426510239534291353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4822659804027305424776941 1808497426510239534291353)
                ·
                  refine ⟨1356373069882679650718515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1808497426510239534291353 1356373069882679650718515)
                  ·
                    refine ⟨2034559604824019476077773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1356373069882679650718515 2034559604824019476077773)
                    ·
                      refine ⟨762959851809007303529165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2034559604824019476077773 762959851809007303529165)
                      ·
                        rfl

theorem cell23_1485859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 3, 2, 1, 3].length) (baseStart_1485859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1485859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1485859 prefixEnd_1485859 := by exact prefixLift 1485859
  have htrace : WordTrace (prefixWord ++ tailWord_1485859) baseStart_1485859 baseEnd_1485859 := by
    simpa [prefixWord, tailWord_1485859, baseEnd_1485859] using wordTrace_append hprefix tailTrace_1485859
  have hstable : (prefixWord ++ tailWord_1485859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485859).length < 2 ^ (prefixWord ++ tailWord_1485859).sum := by decide
  have hdescent : baseEnd_1485859 < baseStart_1485859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485905 : List Nat := [1, 2, 2, 1, 3, 1, 3, 3, 7]
def baseStart_1485905 : Nat := 118140960795 + 1485905 * 2 ^ 59
def prefixEnd_1485905 : Nat := 4983230072969 + 3 ^ 40 * 1485905 * 2
def baseEnd_1485905 : Nat := 84775941324346013728217

theorem tailTrace_1485905 : CollatzResearch.WordTrace tailWord_1485905 prefixEnd_1485905 84775941324346013728217 := by
  unfold tailWord_1485905
  simp only [CollatzResearch.WordTrace]
  refine ⟨54195407681827432215259169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36130271787884954810172779 54195407681827432215259169)
  ·
    refine ⟨40646555761370574161444377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54195407681827432215259169 40646555761370574161444377)
    ·
      refine ⟨30484916821027930621083283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40646555761370574161444377 30484916821027930621083283)
      ·
        refine ⟨45727375231541895931624925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30484916821027930621083283 45727375231541895931624925)
        ·
          refine ⟨17147765711828210974359347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45727375231541895931624925 17147765711828210974359347)
          ·
            refine ⟨25721648567742316461539021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17147765711828210974359347 25721648567742316461539021)
            ·
              refine ⟨9645618212903368673077133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25721648567742316461539021 9645618212903368673077133)
              ·
                refine ⟨3617106829838763252403925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9645618212903368673077133 3617106829838763252403925)
                ·
                  refine ⟨84775941324346013728217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3617106829838763252403925 84775941324346013728217)
                  ·
                    rfl

theorem cell23_1485905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3, 7].length) (baseStart_1485905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1485905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1485905 prefixEnd_1485905 := by exact prefixLift 1485905
  have htrace : WordTrace (prefixWord ++ tailWord_1485905) baseStart_1485905 baseEnd_1485905 := by
    simpa [prefixWord, tailWord_1485905, baseEnd_1485905] using wordTrace_append hprefix tailTrace_1485905
  have hstable : (prefixWord ++ tailWord_1485905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485905).length < 2 ^ (prefixWord ++ tailWord_1485905).sum := by decide
  have hdescent : baseEnd_1485905 < baseStart_1485905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485910 : List Nat := [5, 2, 2, 1, 3, 1, 1, 1, 1, 3, 3]
def baseStart_1485910 : Nat := 118140960795 + 1485910 * 2 ^ 59
def prefixEnd_1485910 : Nat := 4983230072969 + 3 ^ 40 * 1485910 * 2
def baseEnd_1485910 : Nat := 762986039322386603991431

theorem tailTrace_1485910 : CollatzResearch.WordTrace tailWord_1485910 prefixEnd_1485910 762986039322386603991431 := by
  unfold tailWord_1485910
  simp only [CollatzResearch.WordTrace]
  refine ⟨3387224377925582379324449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36130393364539545379460789 3387224377925582379324449)
  ·
    refine ⟨2540418283444186784493337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3387224377925582379324449 2540418283444186784493337)
    ·
      refine ⟨1905313712583140088370003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2540418283444186784493337 1905313712583140088370003)
      ·
        refine ⟨2857970568874710132555005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1905313712583140088370003 2857970568874710132555005)
        ·
          refine ⟨1071738963328016299708127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2857970568874710132555005 1071738963328016299708127)
          ·
            refine ⟨1607608444992024449562191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1071738963328016299708127 1607608444992024449562191)
            ·
              refine ⟨2411412667488036674343287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1607608444992024449562191 2411412667488036674343287)
              ·
                refine ⟨3617119001232055011514931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2411412667488036674343287 3617119001232055011514931)
                ·
                  refine ⟨5425678501848082517272397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3617119001232055011514931 5425678501848082517272397)
                  ·
                    refine ⟨2034629438193030943977149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5425678501848082517272397 2034629438193030943977149)
                    ·
                      refine ⟨762986039322386603991431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2034629438193030943977149 762986039322386603991431)
                      ·
                        rfl

theorem cell23_1485910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_1485910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1485910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1485910 prefixEnd_1485910 := by exact prefixLift 1485910
  have htrace : WordTrace (prefixWord ++ tailWord_1485910) baseStart_1485910 baseEnd_1485910 := by
    simpa [prefixWord, tailWord_1485910, baseEnd_1485910] using wordTrace_append hprefix tailTrace_1485910
  have hstable : (prefixWord ++ tailWord_1485910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485910).length < 2 ^ (prefixWord ++ tailWord_1485910).sum := by decide
  have hdescent : baseEnd_1485910 < baseStart_1485910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485935 : List Nat := [1, 1, 2, 1, 3, 3, 1, 3, 1, 7]
def baseStart_1485935 : Nat := 118140960795 + 1485935 * 2 ^ 59
def prefixEnd_1485935 : Nat := 4983230072969 + 3 ^ 40 * 1485935 * 2
def baseEnd_1485935 : Nat := 254332958779583002059605

theorem tailTrace_1485935 : CollatzResearch.WordTrace tailWord_1485935 prefixEnd_1485935 254332958779583002059605 := by
  unfold tailWord_1485935
  simp only [CollatzResearch.WordTrace]
  refine ⟨54196501871718747338851259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36131001247812498225900839 54196501871718747338851259)
  ·
    refine ⟨81294752807578121008276889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54196501871718747338851259 81294752807578121008276889)
    ·
      refine ⟨60971064605683590756207667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81294752807578121008276889 60971064605683590756207667)
      ·
        refine ⟨91456596908525386134311501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60971064605683590756207667 91456596908525386134311501)
        ·
          refine ⟨34296223840697019800366813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91456596908525386134311501 34296223840697019800366813)
          ·
            refine ⟨12861083940261382425137555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34296223840697019800366813 12861083940261382425137555)
            ·
              refine ⟨19291625910392073637706333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12861083940261382425137555 19291625910392073637706333)
              ·
                refine ⟨7234359716397027614139875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19291625910392073637706333 7234359716397027614139875)
                ·
                  refine ⟨10851539574595541421209813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7234359716397027614139875 10851539574595541421209813)
                  ·
                    refine ⟨254332958779583002059605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10851539574595541421209813 254332958779583002059605)
                    ·
                      rfl

theorem cell23_1485935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 7].length) (baseStart_1485935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1485935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1485935 prefixEnd_1485935 := by exact prefixLift 1485935
  have htrace : WordTrace (prefixWord ++ tailWord_1485935) baseStart_1485935 baseEnd_1485935 := by
    simpa [prefixWord, tailWord_1485935, baseEnd_1485935] using wordTrace_append hprefix tailTrace_1485935
  have hstable : (prefixWord ++ tailWord_1485935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485935).length < 2 ^ (prefixWord ++ tailWord_1485935).sum := by decide
  have hdescent : baseEnd_1485935 < baseStart_1485935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485956 : List Nat := [2, 3, 2, 1, 2, 3, 3, 2, 5]
def baseStart_1485956 : Nat := 118140960795 + 1485956 * 2 ^ 59
def prefixEnd_1485956 : Nat := 4983230072969 + 3 ^ 40 * 1485956 * 2
def baseEnd_1485956 : Nat := 84778851048054824890691

theorem tailTrace_1485956 : CollatzResearch.WordTrace tailWord_1485956 prefixEnd_1485956 84778851048054824890691 := by
  unfold tailWord_1485956
  simp only [CollatzResearch.WordTrace]
  refine ⟨27098633902321333962682861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36131511869761778616910481 27098633902321333962682861)
  ·
    refine ⟨10161987713370500236006073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27098633902321333962682861 10161987713370500236006073)
    ·
      refine ⟨7621490785027875177004555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10161987713370500236006073 7621490785027875177004555)
      ·
        refine ⟨11432236177541812765506833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7621490785027875177004555 11432236177541812765506833)
        ·
          refine ⟨8574177133156359574130125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11432236177541812765506833 8574177133156359574130125)
          ·
            refine ⟨3215316424933634840298797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8574177133156359574130125 3215316424933634840298797)
            ·
              refine ⟨1205743659350113065112049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3215316424933634840298797 1205743659350113065112049)
              ·
                refine ⟨904307744512584798834037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1205743659350113065112049 904307744512584798834037)
                ·
                  refine ⟨84778851048054824890691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 904307744512584798834037 84778851048054824890691)
                  ·
                    rfl

theorem cell23_1485956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 2, 5].length) (baseStart_1485956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1485956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1485956 prefixEnd_1485956 := by exact prefixLift 1485956
  have htrace : WordTrace (prefixWord ++ tailWord_1485956) baseStart_1485956 baseEnd_1485956 := by
    simpa [prefixWord, tailWord_1485956, baseEnd_1485956] using wordTrace_append hprefix tailTrace_1485956
  have hstable : (prefixWord ++ tailWord_1485956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485956).length < 2 ^ (prefixWord ++ tailWord_1485956).sum := by decide
  have hdescent : baseEnd_1485956 < baseStart_1485956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485962 : List Nat := [3, 1, 2, 3, 1, 1, 3, 1, 1, 2, 5]
def baseStart_1485962 : Nat := 118140960795 + 1485962 * 2 ^ 59
def prefixEnd_1485962 : Nat := 4983230072969 + 3 ^ 40 * 1485962 * 2
def baseEnd_1485962 : Nat := 763012740316420400541191

theorem tailTrace_1485962 : CollatzResearch.WordTrace tailWord_1485962 prefixEnd_1485962 763012740316420400541191 := by
  unfold tailWord_1485962
  simp only [CollatzResearch.WordTrace]
  refine ⟨13549371660655232737521035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36131657761747287300056093 13549371660655232737521035)
  ·
    refine ⟨20324057490982849106281553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13549371660655232737521035 20324057490982849106281553)
    ·
      refine ⟨15243043118237136829711165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20324057490982849106281553 15243043118237136829711165)
      ·
        refine ⟨5716141169338926311141687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15243043118237136829711165 5716141169338926311141687)
        ·
          refine ⟨8574211754008389466712531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5716141169338926311141687 8574211754008389466712531)
          ·
            refine ⟨12861317631012584200068797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8574211754008389466712531 12861317631012584200068797)
            ·
              refine ⟨4822994111629719075025799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12861317631012584200068797 4822994111629719075025799)
              ·
                refine ⟨7234491167444578612538699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4822994111629719075025799 7234491167444578612538699)
                ·
                  refine ⟨10851736751166867918808049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7234491167444578612538699 10851736751166867918808049)
                  ·
                    refine ⟨8138802563375150939106037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10851736751166867918808049 8138802563375150939106037)
                    ·
                      refine ⟨763012740316420400541191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8138802563375150939106037 763012740316420400541191)
                      ·
                        rfl

theorem cell23_1485962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_1485962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1485962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1485962 prefixEnd_1485962 := by exact prefixLift 1485962
  have htrace : WordTrace (prefixWord ++ tailWord_1485962) baseStart_1485962 baseEnd_1485962 := by
    simpa [prefixWord, tailWord_1485962, baseEnd_1485962] using wordTrace_append hprefix tailTrace_1485962
  have hstable : (prefixWord ++ tailWord_1485962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485962).length < 2 ^ (prefixWord ++ tailWord_1485962).sum := by decide
  have hdescent : baseEnd_1485962 < baseStart_1485962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485986 : List Nat := [3, 3, 1, 3, 2, 1, 2, 1, 2, 5]
def baseStart_1485986 : Nat := 118140960795 + 1485986 * 2 ^ 59
def prefixEnd_1485986 : Nat := 4983230072969 + 3 ^ 40 * 1485986 * 2
def baseEnd_1485986 : Nat := 254341687950709435547027

theorem tailTrace_1485986 : CollatzResearch.WordTrace tailWord_1485986 prefixEnd_1485986 254341687950709435547027 := by
  unfold tailWord_1485986
  simp only [CollatzResearch.WordTrace]
  refine ⟨13549590498633495762239453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36132241329689322032638541 13549590498633495762239453)
  ·
    refine ⟨5081096436987560910839795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13549590498633495762239453 5081096436987560910839795)
    ·
      refine ⟨7621644655481341366259693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5081096436987560910839795 7621644655481341366259693)
      ·
        refine ⟨2858116745805503012347385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7621644655481341366259693 2858116745805503012347385)
        ·
          refine ⟨2143587559354127259260539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2858116745805503012347385 2143587559354127259260539)
          ·
            refine ⟨3215381339031190888890809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2143587559354127259260539 3215381339031190888890809)
            ·
              refine ⟨2411536004273393166668107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3215381339031190888890809 2411536004273393166668107)
              ·
                refine ⟨3617304006410089750002161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2411536004273393166668107 3617304006410089750002161)
                ·
                  refine ⟨2712978004807567312501621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3617304006410089750002161 2712978004807567312501621)
                  ·
                    refine ⟨254341687950709435547027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2712978004807567312501621 254341687950709435547027)
                    ·
                      rfl

theorem cell23_1485986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_1485986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1485986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1485986 prefixEnd_1485986 := by exact prefixLift 1485986
  have htrace : WordTrace (prefixWord ++ tailWord_1485986) baseStart_1485986 baseEnd_1485986 := by
    simpa [prefixWord, tailWord_1485986, baseEnd_1485986] using wordTrace_append hprefix tailTrace_1485986
  have hstable : (prefixWord ++ tailWord_1485986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485986).length < 2 ^ (prefixWord ++ tailWord_1485986).sum := by decide
  have hdescent : baseEnd_1485986 < baseStart_1485986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485989 : List Nat := [1, 3, 1, 2, 1, 5, 2, 1, 2, 1, 4]
def baseStart_1485989 : Nat := 118140960795 + 1485989 * 2 ^ 59
def prefixEnd_1485989 : Nat := 4983230072969 + 3 ^ 40 * 1485989 * 2
def baseEnd_1485989 : Nat := 763026604294091794903567

theorem tailTrace_1485989 : CollatzResearch.WordTrace tailWord_1485989 prefixEnd_1485989 763026604294091794903567 := by
  unfold tailWord_1485989
  simp only [CollatzResearch.WordTrace]
  refine ⟨54198471413523114561317021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36132314275682076374211347 54198471413523114561317021)
  ·
    refine ⟨20324426780071167960493883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54198471413523114561317021 20324426780071167960493883)
    ·
      refine ⟨30486640170106751940740825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20324426780071167960493883 30486640170106751940740825)
      ·
        refine ⟨22864980127580063955555619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30486640170106751940740825 22864980127580063955555619)
        ·
          refine ⟨34297470191370095933333429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22864980127580063955555619 34297470191370095933333429)
          ·
            refine ⟨3215387830440946493750009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34297470191370095933333429 3215387830440946493750009)
            ·
              refine ⟨2411540872830709870312507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3215387830440946493750009 2411540872830709870312507)
              ·
                refine ⟨3617311309246064805468761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2411540872830709870312507 3617311309246064805468761)
                ·
                  refine ⟨2712983481934548604101571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3617311309246064805468761 2712983481934548604101571)
                  ·
                    refine ⟨4069475222901822906152357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2712983481934548604101571 4069475222901822906152357)
                    ·
                      refine ⟨763026604294091794903567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4069475222901822906152357 763026604294091794903567)
                      ·
                        rfl

theorem cell23_1485989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 1, 2, 1, 4].length) (baseStart_1485989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1485989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1485989 prefixEnd_1485989 := by exact prefixLift 1485989
  have htrace : WordTrace (prefixWord ++ tailWord_1485989) baseStart_1485989 baseEnd_1485989 := by
    simpa [prefixWord, tailWord_1485989, baseEnd_1485989] using wordTrace_append hprefix tailTrace_1485989
  have hstable : (prefixWord ++ tailWord_1485989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485989).length < 2 ^ (prefixWord ++ tailWord_1485989).sum := by decide
  have hdescent : baseEnd_1485989 < baseStart_1485989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486009 : List Nat := [1, 2, 1, 4, 1, 3, 2, 2, 2, 2, 3]
def baseStart_1486009 : Nat := 118140960795 + 1486009 * 2 ^ 59
def prefixEnd_1486009 : Nat := 4983230072969 + 3 ^ 40 * 1486009 * 2
def baseEnd_1486009 : Nat := 763036873907181716653475

theorem tailTrace_1486009 : CollatzResearch.WordTrace tailWord_1486009 prefixEnd_1486009 763036873907181716653475 := by
  unfold tailWord_1486009
  simp only [CollatzResearch.WordTrace]
  refine ⟨54199200873450657977045081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36132800582300438651363387 54199200873450657977045081)
  ·
    refine ⟨40649400655087993482783811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54199200873450657977045081 40649400655087993482783811)
    ·
      refine ⟨60974100982631990224175717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40649400655087993482783811 60974100982631990224175717)
      ·
        refine ⟨11432643934243498167032947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60974100982631990224175717 11432643934243498167032947)
        ·
          refine ⟨17148965901365247250549421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11432643934243498167032947 17148965901365247250549421)
          ·
            refine ⟨6430862213011967718956033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17148965901365247250549421 6430862213011967718956033)
            ·
              refine ⟨4823146659758975789217025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6430862213011967718956033 4823146659758975789217025)
              ·
                refine ⟨3617359994819231841912769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4823146659758975789217025 3617359994819231841912769)
                ·
                  refine ⟨2713019996114423881434577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3617359994819231841912769 2713019996114423881434577)
                  ·
                    refine ⟨2034764997085817911075933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2713019996114423881434577 2034764997085817911075933)
                    ·
                      refine ⟨763036873907181716653475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2034764997085817911075933 763036873907181716653475)
                      ·
                        rfl

theorem cell23_1486009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_1486009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1486009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1486009 prefixEnd_1486009 := by exact prefixLift 1486009
  have htrace : WordTrace (prefixWord ++ tailWord_1486009) baseStart_1486009 baseEnd_1486009 := by
    simpa [prefixWord, tailWord_1486009, baseEnd_1486009] using wordTrace_append hprefix tailTrace_1486009
  have hstable : (prefixWord ++ tailWord_1486009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486009).length < 2 ^ (prefixWord ++ tailWord_1486009).sum := by decide
  have hdescent : baseEnd_1486009 < baseStart_1486009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486039 : List Nat := [1, 1, 3, 2, 1, 2, 3, 1, 5, 1, 3]
def baseStart_1486039 : Nat := 118140960795 + 1486039 * 2 ^ 59
def prefixEnd_1486039 : Nat := 4983230072969 + 3 ^ 40 * 1486039 * 2
def baseEnd_1486039 : Nat := 763052278326816599278337

theorem tailTrace_1486039 : CollatzResearch.WordTrace tailWord_1486039 prefixEnd_1486039 763052278326816599278337 := by
  unfold tailWord_1486039
  simp only [CollatzResearch.WordTrace]
  refine ⟨54200295063341973100637171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36133530042227982067091447 54200295063341973100637171)
  ·
    refine ⟨81300442595012959650955757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54200295063341973100637171 81300442595012959650955757)
    ·
      refine ⟨30487665973129859869108409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81300442595012959650955757 30487665973129859869108409)
      ·
        refine ⟨22865749479847394901831307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30487665973129859869108409 22865749479847394901831307)
        ·
          refine ⟨34298624219771092352746961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22865749479847394901831307 34298624219771092352746961)
          ·
            refine ⟨25723968164828319264560221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34298624219771092352746961 25723968164828319264560221)
            ·
              refine ⟨9646488061810619724210083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25723968164828319264560221 9646488061810619724210083)
              ·
                refine ⟨14469732092715929586315125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9646488061810619724210083 14469732092715929586315125)
                ·
                  refine ⟨1356537383692118398717043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14469732092715929586315125 1356537383692118398717043)
                  ·
                    refine ⟨2034806075538177598075565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1356537383692118398717043 2034806075538177598075565)
                    ·
                      refine ⟨763052278326816599278337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2034806075538177598075565 763052278326816599278337)
                      ·
                        rfl

theorem cell23_1486039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 5, 1, 3].length) (baseStart_1486039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1486039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1486039 prefixEnd_1486039 := by exact prefixLift 1486039
  have htrace : WordTrace (prefixWord ++ tailWord_1486039) baseStart_1486039 baseEnd_1486039 := by
    simpa [prefixWord, tailWord_1486039, baseEnd_1486039] using wordTrace_append hprefix tailTrace_1486039
  have hstable : (prefixWord ++ tailWord_1486039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486039).length < 2 ^ (prefixWord ++ tailWord_1486039).sum := by decide
  have hdescent : baseEnd_1486039 < baseStart_1486039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486059 : List Nat := [1, 1, 1, 1, 2, 7, 1, 3, 1, 5]
def baseStart_1486059 : Nat := 118140960795 + 1486059 * 2 ^ 59
def prefixEnd_1486059 : Nat := 4983230072969 + 3 ^ 40 * 1486059 * 2
def baseEnd_1486059 : Nat := 254354182646635507009415

theorem tailTrace_1486059 : CollatzResearch.WordTrace tailWord_1486059 prefixEnd_1486059 254354182646635507009415 := by
  unfold tailWord_1486059
  simp only [CollatzResearch.WordTrace]
  refine ⟨54201024523269516516365231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36134016348846344344243487 54201024523269516516365231)
  ·
    refine ⟨81301536784904274774547847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54201024523269516516365231 81301536784904274774547847)
    ·
      refine ⟨121952305177356412161821771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81301536784904274774547847 121952305177356412161821771)
      ·
        refine ⟨182928457766034618242732657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121952305177356412161821771 182928457766034618242732657)
        ·
          refine ⟨137196343324525963682049493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182928457766034618242732657 137196343324525963682049493)
          ·
            refine ⟨3215539296668577273798035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 137196343324525963682049493 3215539296668577273798035)
            ·
              refine ⟨4823308945002865910697053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3215539296668577273798035 4823308945002865910697053)
              ·
                refine ⟨1808740854376074716511395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4823308945002865910697053 1808740854376074716511395)
                ·
                  refine ⟨2713111281564112074767093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1808740854376074716511395 2713111281564112074767093)
                  ·
                    refine ⟨254354182646635507009415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2713111281564112074767093 254354182646635507009415)
                    ·
                      rfl

theorem cell23_1486059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 3, 1, 5].length) (baseStart_1486059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1486059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1486059 prefixEnd_1486059 := by exact prefixLift 1486059
  have htrace : WordTrace (prefixWord ++ tailWord_1486059) baseStart_1486059 baseEnd_1486059 := by
    simpa [prefixWord, tailWord_1486059, baseEnd_1486059] using wordTrace_append hprefix tailTrace_1486059
  have hstable : (prefixWord ++ tailWord_1486059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486059).length < 2 ^ (prefixWord ++ tailWord_1486059).sum := by decide
  have hdescent : baseEnd_1486059 < baseStart_1486059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486116 : List Nat := [2, 3, 1, 3, 1, 1, 1, 5, 1, 2, 3]
def baseStart_1486116 : Nat := 118140960795 + 1486116 * 2 ^ 59
def prefixEnd_1486116 : Nat := 4983230072969 + 3 ^ 40 * 1486116 * 2
def baseEnd_1486116 : Nat := 763091816337212798015483

theorem tailTrace_1486116 : CollatzResearch.WordTrace tailWord_1486116 prefixEnd_1486116 763091816337212798015483 := by
  unfold tailWord_1486116
  simp only [CollatzResearch.WordTrace]
  refine ⟨27101551742031507625595101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36135402322708676834126801 27101551742031507625595101)
  ·
    refine ⟨10163081903261815359598163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27101551742031507625595101 10163081903261815359598163)
    ·
      refine ⟨15244622854892723039397245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10163081903261815359598163 15244622854892723039397245)
      ·
        refine ⟨5716733570584771139773967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15244622854892723039397245 5716733570584771139773967)
        ·
          refine ⟨8575100355877156709660951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5716733570584771139773967 8575100355877156709660951)
          ·
            refine ⟨12862650533815735064491427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8575100355877156709660951 12862650533815735064491427)
            ·
              refine ⟨19293975800723602596737141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12862650533815735064491427 19293975800723602596737141)
              ·
                refine ⟨1808810231317837743444107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19293975800723602596737141 1808810231317837743444107)
                ·
                  refine ⟨2713215346976756615166161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1808810231317837743444107 2713215346976756615166161)
                  ·
                    refine ⟨2034911510232567461374621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2713215346976756615166161 2034911510232567461374621)
                    ·
                      refine ⟨763091816337212798015483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2034911510232567461374621 763091816337212798015483)
                      ·
                        rfl

theorem cell23_1486116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_1486116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1486116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1486116 prefixEnd_1486116 := by exact prefixLift 1486116
  have htrace : WordTrace (prefixWord ++ tailWord_1486116) baseStart_1486116 baseEnd_1486116 := by
    simpa [prefixWord, tailWord_1486116, baseEnd_1486116] using wordTrace_append hprefix tailTrace_1486116
  have hstable : (prefixWord ++ tailWord_1486116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486116).length < 2 ^ (prefixWord ++ tailWord_1486116).sum := by decide
  have hdescent : baseEnd_1486116 < baseStart_1486116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486130 : List Nat := [3, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2]
def baseStart_1486130 : Nat := 118140960795 + 1486130 * 2 ^ 59
def prefixEnd_1486130 : Nat := 4983230072969 + 3 ^ 40 * 1486130 * 2
def baseEnd_1486130 : Nat := 763099005066375743240419

theorem tailTrace_1486130 : CollatzResearch.WordTrace tailWord_1486130 prefixEnd_1486130 763099005066375743240419 := by
  unfold tailWord_1486130
  simp only [CollatzResearch.WordTrace]
  refine ⟨13550903526503073910549961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36135742737341530428133229 13550903526503073910549961)
  ·
    refine ⟨10163177644877305432912471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13550903526503073910549961 10163177644877305432912471)
    ·
      refine ⟨15244766467315958149368707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10163177644877305432912471 15244766467315958149368707)
      ·
        refine ⟨22867149700973937224053061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15244766467315958149368707 22867149700973937224053061)
        ·
          refine ⟨4287590568932613229509949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22867149700973937224053061 4287590568932613229509949)
          ·
            refine ⟨1607846463349729961066231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4287590568932613229509949 1607846463349729961066231)
            ·
              refine ⟨2411769695024594941599347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1607846463349729961066231 2411769695024594941599347)
              ·
                refine ⟨3617654542536892412399021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2411769695024594941599347 3617654542536892412399021)
                ·
                  refine ⟨1356620453451334654649633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3617654542536892412399021 1356620453451334654649633)
                  ·
                    refine ⟨1017465340088500990987225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1356620453451334654649633 1017465340088500990987225)
                    ·
                      refine ⟨763099005066375743240419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1017465340088500990987225 763099005066375743240419)
                      ·
                        rfl

theorem cell23_1486130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2].length) (baseStart_1486130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1486130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1486130 prefixEnd_1486130 := by exact prefixLift 1486130
  have htrace : WordTrace (prefixWord ++ tailWord_1486130) baseStart_1486130 baseEnd_1486130 := by
    simpa [prefixWord, tailWord_1486130, baseEnd_1486130] using wordTrace_append hprefix tailTrace_1486130
  have hstable : (prefixWord ++ tailWord_1486130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486130).length < 2 ^ (prefixWord ++ tailWord_1486130).sum := by decide
  have hdescent : baseEnd_1486130 < baseStart_1486130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486152 : List Nat := [2, 1, 3, 1, 1, 2, 1, 1, 1, 2, 8]
def baseStart_1486152 : Nat := 118140960795 + 1486152 * 2 ^ 59
def prefixEnd_1486152 : Nat := 4983230072969 + 3 ^ 40 * 1486152 * 2
def baseEnd_1486152 : Nat := 763110301640774657165317

theorem tailTrace_1486152 : CollatzResearch.WordTrace tailWord_1486152 prefixEnd_1486152 763110301640774657165317 := by
  unfold tailWord_1486152
  simp only [CollatzResearch.WordTrace]
  refine ⟨27102208255966296699750355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36136277674621728933000473 27102208255966296699750355)
  ·
    refine ⟨40653312383949445049625533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27102208255966296699750355 40653312383949445049625533)
    ·
      refine ⟨15244992143981041893609575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40653312383949445049625533 15244992143981041893609575)
      ·
        refine ⟨22867488215971562840414363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15244992143981041893609575 22867488215971562840414363)
        ·
          refine ⟨34301232323957344260621545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22867488215971562840414363 34301232323957344260621545)
          ·
            refine ⟨25725924242968008195466159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34301232323957344260621545 25725924242968008195466159)
            ·
              refine ⟨38588886364452012293199239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25725924242968008195466159 38588886364452012293199239)
              ·
                refine ⟨57883329546678018439798859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38588886364452012293199239 57883329546678018439798859)
                ·
                  refine ⟨86824994320017027659698289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57883329546678018439798859 86824994320017027659698289)
                  ·
                    refine ⟨65118745740012770744773717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 86824994320017027659698289 65118745740012770744773717)
                    ·
                      refine ⟨763110301640774657165317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 65118745740012770744773717 763110301640774657165317)
                      ·
                        rfl

theorem cell23_1486152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_1486152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1486152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1486152 prefixEnd_1486152 := by exact prefixLift 1486152
  have htrace : WordTrace (prefixWord ++ tailWord_1486152) baseStart_1486152 baseEnd_1486152 := by
    simpa [prefixWord, tailWord_1486152, baseEnd_1486152] using wordTrace_append hprefix tailTrace_1486152
  have hstable : (prefixWord ++ tailWord_1486152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486152).length < 2 ^ (prefixWord ++ tailWord_1486152).sum := by decide
  have hdescent : baseEnd_1486152 < baseStart_1486152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486199 : List Nat := [1, 1, 3, 1, 1, 2, 5, 1, 2, 2, 4]
def baseStart_1486199 : Nat := 118140960795 + 1486199 * 2 ^ 59
def prefixEnd_1486199 : Nat := 4983230072969 + 3 ^ 40 * 1486199 * 2
def baseEnd_1486199 : Nat := 763134435231535973277601

theorem tailTrace_1486199 : CollatzResearch.WordTrace tailWord_1486199 prefixEnd_1486199 763134435231535973277601 := by
  unfold tailWord_1486199
  simp only [CollatzResearch.WordTrace]
  refine ⟨54206130742762320426461651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36137420495174880284307767 54206130742762320426461651)
  ·
    refine ⟨81309196114143480639692477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54206130742762320426461651 81309196114143480639692477)
    ·
      refine ⟨30490948542803805239884679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81309196114143480639692477 30490948542803805239884679)
      ·
        refine ⟨45736422814205707859827019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30490948542803805239884679 45736422814205707859827019)
        ·
          refine ⟨68604634221308561789740529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45736422814205707859827019 68604634221308561789740529)
          ·
            refine ⟨51453475665981421342305397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68604634221308561789740529 51453475665981421342305397)
            ·
              refine ⟨4823763343685758250841131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51453475665981421342305397 4823763343685758250841131)
              ·
                refine ⟨7235645015528637376261697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4823763343685758250841131 7235645015528637376261697)
                ·
                  refine ⟨5426733761646478032196273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7235645015528637376261697 5426733761646478032196273)
                  ·
                    refine ⟨4070050321234858524147205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5426733761646478032196273 4070050321234858524147205)
                    ·
                      refine ⟨763134435231535973277601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4070050321234858524147205 763134435231535973277601)
                      ·
                        rfl

theorem cell23_1486199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 2, 2, 4].length) (baseStart_1486199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1486199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1486199 prefixEnd_1486199 := by exact prefixLift 1486199
  have htrace : WordTrace (prefixWord ++ tailWord_1486199) baseStart_1486199 baseEnd_1486199 := by
    simpa [prefixWord, tailWord_1486199, baseEnd_1486199] using wordTrace_append hprefix tailTrace_1486199
  have hstable : (prefixWord ++ tailWord_1486199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486199).length < 2 ^ (prefixWord ++ tailWord_1486199).sum := by decide
  have hdescent : baseEnd_1486199 < baseStart_1486199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486203 : List Nat := [1, 1, 1, 1, 1, 6, 1, 5, 2, 2, 2]
def baseStart_1486203 : Nat := 118140960795 + 1486203 * 2 ^ 59
def prefixEnd_1486203 : Nat := 4983230072969 + 3 ^ 40 * 1486203 * 2
def baseEnd_1486203 : Nat := 763136489154153957627583

theorem tailTrace_1486203 : CollatzResearch.WordTrace tailWord_1486203 prefixEnd_1486203 763136489154153957627583 := by
  unfold tailWord_1486203
  simp only [CollatzResearch.WordTrace]
  refine ⟨54206276634747829109607263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36137517756498552739738175 54206276634747829109607263)
  ·
    refine ⟨81309414952121743664410895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54206276634747829109607263 81309414952121743664410895)
    ·
      refine ⟨121964122428182615496616343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81309414952121743664410895 121964122428182615496616343)
      ·
        refine ⟨182946183642273923244924515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121964122428182615496616343 182946183642273923244924515)
        ·
          refine ⟨274419275463410884867386773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182946183642273923244924515 274419275463410884867386773)
          ·
            refine ⟨12863403537347385228158755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 274419275463410884867386773 12863403537347385228158755)
            ·
              refine ⟨19295105306021077842238133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12863403537347385228158755 19295105306021077842238133)
              ·
                refine ⟨1808916122439476047709825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19295105306021077842238133 1808916122439476047709825)
                ·
                  refine ⟨1356687091829607035782369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1808916122439476047709825 1356687091829607035782369)
                  ·
                    refine ⟨1017515318872205276836777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1356687091829607035782369 1017515318872205276836777)
                    ·
                      refine ⟨763136489154153957627583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1017515318872205276836777 763136489154153957627583)
                      ·
                        rfl

theorem cell23_1486203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 5, 2, 2, 2].length) (baseStart_1486203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1486203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1486203 prefixEnd_1486203 := by exact prefixLift 1486203
  have htrace : WordTrace (prefixWord ++ tailWord_1486203) baseStart_1486203 baseEnd_1486203 := by
    simpa [prefixWord, tailWord_1486203, baseEnd_1486203] using wordTrace_append hprefix tailTrace_1486203
  have hstable : (prefixWord ++ tailWord_1486203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486203).length < 2 ^ (prefixWord ++ tailWord_1486203).sum := by decide
  have hdescent : baseEnd_1486203 < baseStart_1486203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486219 : List Nat := [1, 1, 1, 1, 4, 3, 1, 2, 1, 5, 3]
def baseStart_1486219 : Nat := 118140960795 + 1486219 * 2 ^ 59
def prefixEnd_1486219 : Nat := 4983230072969 + 3 ^ 40 * 1486219 * 2
def baseEnd_1486219 : Nat := 763144704844625895027509

theorem tailTrace_1486219 : CollatzResearch.WordTrace tailWord_1486219 prefixEnd_1486219 763144704844625895027509 := by
  unfold tailWord_1486219
  simp only [CollatzResearch.WordTrace]
  refine ⟨54206860202689863842189711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36137906801793242561459807 54206860202689863842189711)
  ·
    refine ⟨81310290304034795763284567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54206860202689863842189711 81310290304034795763284567)
    ·
      refine ⟨121965435456052193644926851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81310290304034795763284567 121965435456052193644926851)
      ·
        refine ⟨182948153184078290467390277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121965435456052193644926851 182948153184078290467390277)
        ·
          refine ⟨34302778722014679462635677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 182948153184078290467390277 34302778722014679462635677)
          ·
            refine ⟨12863542020755504798488379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34302778722014679462635677 12863542020755504798488379)
            ·
              refine ⟨19295313031133257197732569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12863542020755504798488379 19295313031133257197732569)
              ·
                refine ⟨14471484773349942898299427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19295313031133257197732569 14471484773349942898299427)
                ·
                  refine ⟨21707227160024914347449141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14471484773349942898299427 21707227160024914347449141)
                  ·
                    refine ⟨2035052546252335720073357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21707227160024914347449141 2035052546252335720073357)
                    ·
                      refine ⟨763144704844625895027509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2035052546252335720073357 763144704844625895027509)
                      ·
                        rfl

theorem cell23_1486219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 5, 3].length) (baseStart_1486219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1486219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1486219 prefixEnd_1486219 := by exact prefixLift 1486219
  have htrace : WordTrace (prefixWord ++ tailWord_1486219) baseStart_1486219 baseEnd_1486219 := by
    simpa [prefixWord, tailWord_1486219, baseEnd_1486219] using wordTrace_append hprefix tailTrace_1486219
  have hstable : (prefixWord ++ tailWord_1486219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486219).length < 2 ^ (prefixWord ++ tailWord_1486219).sum := by decide
  have hdescent : baseEnd_1486219 < baseStart_1486219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486237 : List Nat := [1, 4, 2, 1, 3, 3, 1, 2, 2, 2, 2]
def baseStart_1486237 : Nat := 118140960795 + 1486237 * 2 ^ 59
def prefixEnd_1486237 : Nat := 4983230072969 + 3 ^ 40 * 1486237 * 2
def baseEnd_1486237 : Nat := 763153947496406824602427

theorem tailTrace_1486237 : CollatzResearch.WordTrace tailWord_1486237 prefixEnd_1486237 763153947496406824602427 := by
  unfold tailWord_1486237
  simp only [CollatzResearch.WordTrace]
  refine ⟨54207516716624652916344965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36138344477749768610896643 54207516716624652916344965)
  ·
    refine ⟨10163909384367122421814681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54207516716624652916344965 10163909384367122421814681)
    ·
      refine ⟨7622932038275341816361011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10163909384367122421814681 7622932038275341816361011)
      ·
        refine ⟨11434398057413012724541517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7622932038275341816361011 11434398057413012724541517)
        ·
          refine ⟨4287899271529879771703069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11434398057413012724541517 4287899271529879771703069)
          ·
            refine ⟨1607962226823704914388651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4287899271529879771703069 1607962226823704914388651)
            ·
              refine ⟨2411943340235557371582977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1607962226823704914388651 2411943340235557371582977)
              ·
                refine ⟨1808957505176668028687233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2411943340235557371582977 1808957505176668028687233)
                ·
                  refine ⟨1356718128882501021515425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1808957505176668028687233 1356718128882501021515425)
                  ·
                    refine ⟨1017538596661875766136569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1356718128882501021515425 1017538596661875766136569)
                    ·
                      refine ⟨763153947496406824602427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1017538596661875766136569 763153947496406824602427)
                      ·
                        rfl

theorem cell23_1486237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 2, 2, 2, 2].length) (baseStart_1486237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1486237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1486237 prefixEnd_1486237 := by exact prefixLift 1486237
  have htrace : WordTrace (prefixWord ++ tailWord_1486237) baseStart_1486237 baseEnd_1486237 := by
    simpa [prefixWord, tailWord_1486237, baseEnd_1486237] using wordTrace_append hprefix tailTrace_1486237
  have hstable : (prefixWord ++ tailWord_1486237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486237).length < 2 ^ (prefixWord ++ tailWord_1486237).sum := by decide
  have hdescent : baseEnd_1486237 < baseStart_1486237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486253 : List Nat := [1, 5, 2, 2, 1, 1, 2, 1, 2, 3, 3]
def baseStart_1486253 : Nat := 118140960795 + 1486253 * 2 ^ 59
def prefixEnd_1486253 : Nat := 4983230072969 + 3 ^ 40 * 1486253 * 2
def baseEnd_1486253 : Nat := 763162163186878762002353

theorem tailTrace_1486253 : CollatzResearch.WordTrace tailWord_1486253 prefixEnd_1486253 763162163186878762002353 := by
  unfold tailWord_1486253
  simp only [CollatzResearch.WordTrace]
  refine ⟨54208100284566687648927413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36138733523044458432618275 54208100284566687648927413)
  ·
    refine ⟨5082009401678126967086945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54208100284566687648927413 5082009401678126967086945)
    ·
      refine ⟨3811507051258595225315209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5082009401678126967086945 3811507051258595225315209)
      ·
        refine ⟨2858630288443946418986407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3811507051258595225315209 2858630288443946418986407)
        ·
          refine ⟨4287945432665919628479611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2858630288443946418986407 4287945432665919628479611)
          ·
            refine ⟨6431918148998879442719417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4287945432665919628479611 6431918148998879442719417)
            ·
              refine ⟨4823938611749159582039563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6431918148998879442719417 4823938611749159582039563)
              ·
                refine ⟨7235907917623739373059345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4823938611749159582039563 7235907917623739373059345)
                ·
                  refine ⟨5426930938217804529794509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7235907917623739373059345 5426930938217804529794509)
                  ·
                    refine ⟨2035099101831676698672941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5426930938217804529794509 2035099101831676698672941)
                    ·
                      refine ⟨763162163186878762002353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2035099101831676698672941 763162163186878762002353)
                      ·
                        rfl

theorem cell23_1486253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_1486253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1486253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1486253 prefixEnd_1486253 := by exact prefixLift 1486253
  have htrace : WordTrace (prefixWord ++ tailWord_1486253) baseStart_1486253 baseEnd_1486253 := by
    simpa [prefixWord, tailWord_1486253, baseEnd_1486253] using wordTrace_append hprefix tailTrace_1486253
  have hstable : (prefixWord ++ tailWord_1486253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486253).length < 2 ^ (prefixWord ++ tailWord_1486253).sum := by decide
  have hdescent : baseEnd_1486253 < baseStart_1486253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486269 : List Nat := [1, 4, 1, 2, 2, 1, 1, 1, 2, 8]
def baseStart_1486269 : Nat := 118140960795 + 1486269 * 2 ^ 59
def prefixEnd_1486269 : Nat := 4983230072969 + 3 ^ 40 * 1486269 * 2
def baseEnd_1486269 : Nat := 254390126292450233134093

theorem tailTrace_1486269 : CollatzResearch.WordTrace tailWord_1486269 prefixEnd_1486269 254390126292450233134093 := by
  unfold tailWord_1486269
  simp only [CollatzResearch.WordTrace]
  refine ⟨54208683852508722381509861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36139122568339148254339907 54208683852508722381509861)
  ·
    refine ⟨10164128222345385446533099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54208683852508722381509861 10164128222345385446533099)
    ·
      refine ⟨15246192333518078169799649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10164128222345385446533099 15246192333518078169799649)
      ·
        refine ⟨11434644250138558627349737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15246192333518078169799649 11434644250138558627349737)
        ·
          refine ⟨8575983187603918970512303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11434644250138558627349737 8575983187603918970512303)
          ·
            refine ⟨12863974781405878455768455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8575983187603918970512303 12863974781405878455768455)
            ·
              refine ⟨19295962172108817683652683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12863974781405878455768455 19295962172108817683652683)
              ·
                refine ⟨28943943258163226525479025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19295962172108817683652683 28943943258163226525479025)
                ·
                  refine ⟨21707957443622419894109269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28943943258163226525479025 21707957443622419894109269)
                  ·
                    refine ⟨254390126292450233134093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 21707957443622419894109269 254390126292450233134093)
                    ·
                      rfl

theorem cell23_1486269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 8].length) (baseStart_1486269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1486269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1486269 prefixEnd_1486269 := by exact prefixLift 1486269
  have htrace : WordTrace (prefixWord ++ tailWord_1486269) baseStart_1486269 baseEnd_1486269 := by
    simpa [prefixWord, tailWord_1486269, baseEnd_1486269] using wordTrace_append hprefix tailTrace_1486269
  have hstable : (prefixWord ++ tailWord_1486269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486269).length < 2 ^ (prefixWord ++ tailWord_1486269).sum := by decide
  have hdescent : baseEnd_1486269 < baseStart_1486269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486286 : List Nat := [4, 1, 1, 1, 2, 1, 2, 2, 5, 4]
def baseStart_1486286 : Nat := 118140960795 + 1486286 * 2 ^ 59
def prefixEnd_1486286 : Nat := 4983230072969 + 3 ^ 40 * 1486286 * 2
def baseEnd_1486286 : Nat := 254393036016159044296567

theorem tailTrace_1486286 : CollatzResearch.WordTrace tailWord_1486286 prefixEnd_1486286 254393036016159044296567 := by
  unfold tailWord_1486286
  simp only [CollatzResearch.WordTrace]
  refine ⟨6776162986680891785609839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36139535928964756189919141 6776162986680891785609839)
  ·
    refine ⟨10164244480021337678414759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6776162986680891785609839 10164244480021337678414759)
    ·
      refine ⟨15246366720032006517622139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10164244480021337678414759 15246366720032006517622139)
      ·
        refine ⟨22869550080048009776433209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15246366720032006517622139 22869550080048009776433209)
        ·
          refine ⟨17152162560036007332324907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22869550080048009776433209 17152162560036007332324907)
          ·
            refine ⟨25728243840054010998487361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17152162560036007332324907 25728243840054010998487361)
            ·
              refine ⟨19296182880040508248865521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25728243840054010998487361 19296182880040508248865521)
              ·
                refine ⟨14472137160030381186649141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19296182880040508248865521 14472137160030381186649141)
                ·
                  refine ⟨1356762858752848236248357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14472137160030381186649141 1356762858752848236248357)
                  ·
                    refine ⟨254393036016159044296567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1356762858752848236248357 254393036016159044296567)
                    ·
                      rfl

theorem cell23_1486286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 5, 4].length) (baseStart_1486286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1486286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1486286 prefixEnd_1486286 := by exact prefixLift 1486286
  have htrace : WordTrace (prefixWord ++ tailWord_1486286) baseStart_1486286 baseEnd_1486286 := by
    simpa [prefixWord, tailWord_1486286, baseEnd_1486286] using wordTrace_append hprefix tailTrace_1486286
  have hstable : (prefixWord ++ tailWord_1486286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486286).length < 2 ^ (prefixWord ++ tailWord_1486286).sum := by decide
  have hdescent : baseEnd_1486286 < baseStart_1486286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486296 : List Nat := [2, 1, 2, 2, 2, 1, 3, 1, 4, 2, 3]
def baseStart_1486296 : Nat := 118140960795 + 1486296 * 2 ^ 59
def prefixEnd_1486296 : Nat := 4983230072969 + 3 ^ 40 * 1486296 * 2
def baseEnd_1486296 : Nat := 763184242855022093764655

theorem tailTrace_1486296 : CollatzResearch.WordTrace tailWord_1486296 prefixEnd_1486296 763184242855022093764655 := by
  unfold tailWord_1486296
  simp only [CollatzResearch.WordTrace]
  refine ⟨27104834311705452996371371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36139779082273937328495161 27104834311705452996371371)
  ·
    refine ⟨40657251467558179494557057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27104834311705452996371371 40657251467558179494557057)
    ·
      refine ⟨30492938600668634620917793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40657251467558179494557057 30492938600668634620917793)
      ·
        refine ⟨22869703950501475965688345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30492938600668634620917793 22869703950501475965688345)
        ·
          refine ⟨17152277962876106974266259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22869703950501475965688345 17152277962876106974266259)
          ·
            refine ⟨25728416944314160461399389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17152277962876106974266259 25728416944314160461399389)
            ·
              refine ⟨9648156354117810173024771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25728416944314160461399389 9648156354117810173024771)
              ·
                refine ⟨14472234531176715259537157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9648156354117810173024771 14472234531176715259537157)
                ·
                  refine ⟨2713543974595634111163217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14472234531176715259537157 2713543974595634111163217)
                  ·
                    refine ⟨2035157980946725583372413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2713543974595634111163217 2035157980946725583372413)
                    ·
                      refine ⟨763184242855022093764655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2035157980946725583372413 763184242855022093764655)
                      ·
                        rfl

theorem cell23_1486296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 4, 2, 3].length) (baseStart_1486296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1486296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1486296 prefixEnd_1486296 := by exact prefixLift 1486296
  have htrace : WordTrace (prefixWord ++ tailWord_1486296) baseStart_1486296 baseEnd_1486296 := by
    simpa [prefixWord, tailWord_1486296, baseEnd_1486296] using wordTrace_append hprefix tailTrace_1486296
  have hstable : (prefixWord ++ tailWord_1486296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486296).length < 2 ^ (prefixWord ++ tailWord_1486296).sum := by decide
  have hdescent : baseEnd_1486296 < baseStart_1486296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486319 : List Nat := [1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 6]
def baseStart_1486319 : Nat := 118140960795 + 1486319 * 2 ^ 59
def prefixEnd_1486319 : Nat := 4983230072969 + 3 ^ 40 * 1486319 * 2
def baseEnd_1486319 : Nat := 763196052910075503777049

theorem tailTrace_1486319 : CollatzResearch.WordTrace tailWord_1486319 prefixEnd_1486319 763196052910075503777049 := by
  unfold tailWord_1486319
  simp only [CollatzResearch.WordTrace]
  refine ⟨54210507502327580920830011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36140338334885053947220007 54210507502327580920830011)
  ·
    refine ⟨81315761253491371381245017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54210507502327580920830011 81315761253491371381245017)
    ·
      refine ⟨60986820940118528535933763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81315761253491371381245017 60986820940118528535933763)
      ·
        refine ⟨91480231410177792803900645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60986820940118528535933763 91480231410177792803900645)
        ·
          refine ⟨17152543389408336150731371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91480231410177792803900645 17152543389408336150731371)
          ·
            refine ⟨25728815084112504226097057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17152543389408336150731371 25728815084112504226097057)
            ·
              refine ⟨19296611313084378169572793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25728815084112504226097057 19296611313084378169572793)
              ·
                refine ⟨14472458484813283627179595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19296611313084378169572793 14472458484813283627179595)
                ·
                  refine ⟨21708687727219925440769393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14472458484813283627179595 21708687727219925440769393)
                  ·
                    refine ⟨16281515795414944080577045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21708687727219925440769393 16281515795414944080577045)
                    ·
                      refine ⟨763196052910075503777049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16281515795414944080577045 763196052910075503777049)
                      ·
                        rfl

theorem cell23_1486319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 6].length) (baseStart_1486319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1486319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1486319 prefixEnd_1486319 := by exact prefixLift 1486319
  have htrace : WordTrace (prefixWord ++ tailWord_1486319) baseStart_1486319 baseEnd_1486319 := by
    simpa [prefixWord, tailWord_1486319, baseEnd_1486319] using wordTrace_append hprefix tailTrace_1486319
  have hstable : (prefixWord ++ tailWord_1486319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486319).length < 2 ^ (prefixWord ++ tailWord_1486319).sum := by decide
  have hdescent : baseEnd_1486319 < baseStart_1486319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486339 : List Nat := [1, 1, 1, 3, 2, 1, 2, 1, 2, 4, 5]
def baseStart_1486339 : Nat := 118140960795 + 1486339 * 2 ^ 59
def prefixEnd_1486339 : Nat := 4983230072969 + 3 ^ 40 * 1486339 * 2
def baseEnd_1486339 : Nat := 763206322523165425526957

theorem tailTrace_1486339 : CollatzResearch.WordTrace tailWord_1486339 prefixEnd_1486339 763206322523165425526957 := by
  unfold tailWord_1486339
  simp only [CollatzResearch.WordTrace]
  refine ⟨54211236962255124336558071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36140824641503416224372047 54211236962255124336558071)
  ·
    refine ⟨81316855443382686504837107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54211236962255124336558071 81316855443382686504837107)
    ·
      refine ⟨121975283165074029757255661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81316855443382686504837107 121975283165074029757255661)
      ·
        refine ⟨45740731186902761158970873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121975283165074029757255661 45740731186902761158970873)
        ·
          refine ⟨34305548390177070869228155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45740731186902761158970873 34305548390177070869228155)
          ·
            refine ⟨51458322585265606303842233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34305548390177070869228155 51458322585265606303842233)
            ·
              refine ⟨38593741938949204727881675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51458322585265606303842233 38593741938949204727881675)
              ·
                refine ⟨57890612908423807091822513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38593741938949204727881675 57890612908423807091822513)
                ·
                  refine ⟨43417959681317855318866885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57890612908423807091822513 43417959681317855318866885)
                  ·
                    refine ⟨8140867440247097872287541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43417959681317855318866885 8140867440247097872287541)
                    ·
                      refine ⟨763206322523165425526957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8140867440247097872287541 763206322523165425526957)
                      ·
                        rfl

theorem cell23_1486339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4, 5].length) (baseStart_1486339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1486339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1486339 prefixEnd_1486339 := by exact prefixLift 1486339
  have htrace : WordTrace (prefixWord ++ tailWord_1486339) baseStart_1486339 baseEnd_1486339 := by
    simpa [prefixWord, tailWord_1486339, baseEnd_1486339] using wordTrace_append hprefix tailTrace_1486339
  have hstable : (prefixWord ++ tailWord_1486339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486339).length < 2 ^ (prefixWord ++ tailWord_1486339).sum := by decide
  have hdescent : baseEnd_1486339 < baseStart_1486339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486353 : List Nat := [1, 2, 2, 1, 1, 2, 3, 4, 2, 3, 2]
def baseStart_1486353 : Nat := 118140960795 + 1486353 * 2 ^ 59
def prefixEnd_1486353 : Nat := 4983230072969 + 3 ^ 40 * 1486353 * 2
def baseEnd_1486353 : Nat := 763213511252328370751893

theorem tailTrace_1486353 : CollatzResearch.WordTrace tailWord_1486353 prefixEnd_1486353 763213511252328370751893 := by
  unfold tailWord_1486353
  simp only [CollatzResearch.WordTrace]
  refine ⟨54211747584204404727567713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36141165056136269818378475 54211747584204404727567713)
  ·
    refine ⟨40658810688153303545675785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54211747584204404727567713 40658810688153303545675785)
    ·
      refine ⟨30494108016114977659256839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40658810688153303545675785 30494108016114977659256839)
      ·
        refine ⟨45741162024172466488885259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30494108016114977659256839 45741162024172466488885259)
        ·
          refine ⟨68611743036258699733327889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45741162024172466488885259 68611743036258699733327889)
          ·
            refine ⟨51458807277194024799995917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68611743036258699733327889 51458807277194024799995917)
            ·
              refine ⟨19297052728947759299998469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51458807277194024799995917 19297052728947759299998469)
              ·
                refine ⟨3618197386677704868749713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19297052728947759299998469 3618197386677704868749713)
                ·
                  refine ⟨2713648040008278651562285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3618197386677704868749713 2713648040008278651562285)
                  ·
                    refine ⟨1017618015003104494335857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2713648040008278651562285 1017618015003104494335857)
                    ·
                      refine ⟨763213511252328370751893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1017618015003104494335857 763213511252328370751893)
                      ·
                        rfl

theorem cell23_1486353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 3, 2].length) (baseStart_1486353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1486353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1486353 prefixEnd_1486353 := by exact prefixLift 1486353
  have htrace : WordTrace (prefixWord ++ tailWord_1486353) baseStart_1486353 baseEnd_1486353 := by
    simpa [prefixWord, tailWord_1486353, baseEnd_1486353] using wordTrace_append hprefix tailTrace_1486353
  have hstable : (prefixWord ++ tailWord_1486353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486353).length < 2 ^ (prefixWord ++ tailWord_1486353).sum := by decide
  have hdescent : baseEnd_1486353 < baseStart_1486353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486397 : List Nat := [1, 4, 1, 3, 3, 2, 2, 1, 1, 5]
def baseStart_1486397 : Nat := 118140960795 + 1486397 * 2 ^ 59
def prefixEnd_1486397 : Nat := 4983230072969 + 3 ^ 40 * 1486397 * 2
def baseEnd_1486397 : Nat := 254412034800375399533897

theorem tailTrace_1486397 : CollatzResearch.WordTrace tailWord_1486397 prefixEnd_1486397 254412034800375399533897 := by
  unfold tailWord_1486397
  simp only [CollatzResearch.WordTrace]
  refine ⟨54213352396045000242169445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36142234930696666828112963 54213352396045000242169445)
  ·
    refine ⟨10165003574258437545406771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54213352396045000242169445 10165003574258437545406771)
    ·
      refine ⟨15247505361387656318110157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10165003574258437545406771 15247505361387656318110157)
      ·
        refine ⟨5717814510520371119291309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15247505361387656318110157 5717814510520371119291309)
        ·
          refine ⟨2144180441445139169734241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5717814510520371119291309 2144180441445139169734241)
          ·
            refine ⟨1608135331083854377300681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2144180441445139169734241 1608135331083854377300681)
            ·
              refine ⟨1206101498312890782975511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1608135331083854377300681 1206101498312890782975511)
              ·
                refine ⟨1809152247469336174463267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1206101498312890782975511 1809152247469336174463267)
                ·
                  refine ⟨2713728371204004261694901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1809152247469336174463267 2713728371204004261694901)
                  ·
                    refine ⟨254412034800375399533897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2713728371204004261694901 254412034800375399533897)
                    ·
                      rfl

theorem cell23_1486397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 1, 1, 5].length) (baseStart_1486397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1486397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1486397 prefixEnd_1486397 := by exact prefixLift 1486397
  have htrace : WordTrace (prefixWord ++ tailWord_1486397) baseStart_1486397 baseEnd_1486397 := by
    simpa [prefixWord, tailWord_1486397, baseEnd_1486397] using wordTrace_append hprefix tailTrace_1486397
  have hstable : (prefixWord ++ tailWord_1486397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486397).length < 2 ^ (prefixWord ++ tailWord_1486397).sum := by decide
  have hdescent : baseEnd_1486397 < baseStart_1486397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486417 : List Nat := [1, 2, 2, 1, 3, 2, 1, 6, 1, 2, 2]
def baseStart_1486417 : Nat := 118140960795 + 1486417 * 2 ^ 59
def prefixEnd_1486417 : Nat := 4983230072969 + 3 ^ 40 * 1486417 * 2
def baseEnd_1486417 : Nat := 763246374014216120351599

theorem tailTrace_1486417 : CollatzResearch.WordTrace tailWord_1486417 prefixEnd_1486417 763246374014216120351599 := by
  unfold tailWord_1486417
  simp only [CollatzResearch.WordTrace]
  refine ⟨54214081855972543657897505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36142721237315029105265003 54214081855972543657897505)
  ·
    refine ⟨40660561391979407743423129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54214081855972543657897505 40660561391979407743423129)
    ·
      refine ⟨30495421043984555807567347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40660561391979407743423129 30495421043984555807567347)
      ·
        refine ⟨45743131565976833711351021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30495421043984555807567347 45743131565976833711351021)
        ·
          refine ⟨17153674337241312641756633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45743131565976833711351021 17153674337241312641756633)
          ·
            refine ⟨12865255752930984481317475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17153674337241312641756633 12865255752930984481317475)
            ·
              refine ⟨19297883629396476721976213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12865255752930984481317475 19297883629396476721976213)
              ·
                refine ⟨904588295127959846342635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19297883629396476721976213 904588295127959846342635)
                ·
                  refine ⟨1356882442691939769513953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 904588295127959846342635 1356882442691939769513953)
                  ·
                    refine ⟨1017661832018954827135465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1356882442691939769513953 1017661832018954827135465)
                    ·
                      refine ⟨763246374014216120351599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1017661832018954827135465 763246374014216120351599)
                      ·
                        rfl

theorem cell23_1486417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 6, 1, 2, 2].length) (baseStart_1486417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1486417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1486417 prefixEnd_1486417 := by exact prefixLift 1486417
  have htrace : WordTrace (prefixWord ++ tailWord_1486417) baseStart_1486417 baseEnd_1486417 := by
    simpa [prefixWord, tailWord_1486417, baseEnd_1486417] using wordTrace_append hprefix tailTrace_1486417
  have hstable : (prefixWord ++ tailWord_1486417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486417).length < 2 ^ (prefixWord ++ tailWord_1486417).sum := by decide
  have hdescent : baseEnd_1486417 < baseStart_1486417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486440 : List Nat := [2, 1, 4, 3, 1, 3, 2, 7]
def baseStart_1486440 : Nat := 118140960795 + 1486440 * 2 ^ 59
def prefixEnd_1486440 : Nat := 4983230072969 + 3 ^ 40 * 1486440 * 2
def baseEnd_1486440 : Nat := 28268821632195167791259

theorem tailTrace_1486440 : CollatzResearch.WordTrace tailWord_1486440 prefixEnd_1486440 28268821632195167791259 := by
  unfold tailWord_1486440
  simp only [CollatzResearch.WordTrace]
  refine ⟨27107460367444609292992387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36143280489926145723989849 27107460367444609292992387)
  ·
    refine ⟨40661190551166913939488581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27107460367444609292992387 40661190551166913939488581)
    ·
      refine ⟨7623973228343796363654109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40661190551166913939488581 7623973228343796363654109)
      ·
        refine ⟨2858989960628923636370291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7623973228343796363654109 2858989960628923636370291)
        ·
          refine ⟨4288484940943385454555437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2858989960628923636370291 4288484940943385454555437)
          ·
            refine ⟨1608181852853769545458289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4288484940943385454555437 1608181852853769545458289)
            ·
              refine ⟨1206136389640327159093717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1608181852853769545458289 1206136389640327159093717)
              ·
                refine ⟨28268821632195167791259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1206136389640327159093717 28268821632195167791259)
                ·
                  rfl

theorem cell23_1486440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 7].length) (baseStart_1486440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1486440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1486440 prefixEnd_1486440 := by exact prefixLift 1486440
  have htrace : WordTrace (prefixWord ++ tailWord_1486440) baseStart_1486440 baseEnd_1486440 := by
    simpa [prefixWord, tailWord_1486440, baseEnd_1486440] using wordTrace_append hprefix tailTrace_1486440
  have hstable : (prefixWord ++ tailWord_1486440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486440).length < 2 ^ (prefixWord ++ tailWord_1486440).sum := by decide
  have hdescent : baseEnd_1486440 < baseStart_1486440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486443 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 7, 3, 2]
def baseStart_1486443 : Nat := 118140960795 + 1486443 * 2 ^ 59
def prefixEnd_1486443 : Nat := 4983230072969 + 3 ^ 40 * 1486443 * 2
def baseEnd_1486443 : Nat := 763259724511233018626479

theorem tailTrace_1486443 : CollatzResearch.WordTrace tailWord_1486443 prefixEnd_1486443 763259724511233018626479 := by
  unfold tailWord_1486443
  simp only [CollatzResearch.WordTrace]
  refine ⟨54215030153878350098343983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36143353435918900065562655 54215030153878350098343983)
  ·
    refine ⟨81322545230817525147515975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54215030153878350098343983 81322545230817525147515975)
    ·
      refine ⟨121983817846226287721273963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81322545230817525147515975 121983817846226287721273963)
      ·
        refine ⟨182975726769339431581910945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121983817846226287721273963 182975726769339431581910945)
        ·
          refine ⟨137231795077004573686433209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182975726769339431581910945 137231795077004573686433209)
          ·
            refine ⟨102923846307753430264824907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137231795077004573686433209 102923846307753430264824907)
            ·
              refine ⟨154385769461630145397237361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102923846307753430264824907 154385769461630145397237361)
              ·
                refine ⟨115789327096222609047928021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154385769461630145397237361 115789327096222609047928021)
                ·
                  refine ⟨2713812353817717399560813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 115789327096222609047928021 2713812353817717399560813)
                  ·
                    refine ⟨1017679632681644024835305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2713812353817717399560813 1017679632681644024835305)
                    ·
                      refine ⟨763259724511233018626479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1017679632681644024835305 763259724511233018626479)
                      ·
                        rfl

theorem cell23_1486443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 7, 3, 2].length) (baseStart_1486443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1486443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1486443 prefixEnd_1486443 := by exact prefixLift 1486443
  have htrace : WordTrace (prefixWord ++ tailWord_1486443) baseStart_1486443 baseEnd_1486443 := by
    simpa [prefixWord, tailWord_1486443, baseEnd_1486443] using wordTrace_append hprefix tailTrace_1486443
  have hstable : (prefixWord ++ tailWord_1486443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486443).length < 2 ^ (prefixWord ++ tailWord_1486443).sum := by decide
  have hdescent : baseEnd_1486443 < baseStart_1486443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486450 : List Nat := [3, 2, 1, 2, 3, 1, 1, 2, 4, 1, 3]
def baseStart_1486450 : Nat := 118140960795 + 1486450 * 2 ^ 59
def prefixEnd_1486450 : Nat := 4983230072969 + 3 ^ 40 * 1486450 * 2
def baseEnd_1486450 : Nat := 763263318875814491238947

theorem tailTrace_1486450 : CollatzResearch.WordTrace tailWord_1486450 prefixEnd_1486450 763263318875814491238947 := by
  unfold tailWord_1486450
  simp only [CollatzResearch.WordTrace]
  refine ⟨13553821366213247573462201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36143523643235326862565869 13553821366213247573462201)
  ·
    refine ⟨10165366024659935680096651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13553821366213247573462201 10165366024659935680096651)
    ·
      refine ⟨15248049036989903520144977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10165366024659935680096651 15248049036989903520144977)
      ·
        refine ⟨11436036777742427640108733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15248049036989903520144977 11436036777742427640108733)
        ·
          refine ⟨4288513791653410365040775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11436036777742427640108733 4288513791653410365040775)
          ·
            refine ⟨6432770687480115547561163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4288513791653410365040775 6432770687480115547561163)
            ·
              refine ⟨9649156031220173321341745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6432770687480115547561163 9649156031220173321341745)
              ·
                refine ⟨7236867023415129991006309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9649156031220173321341745 7236867023415129991006309)
                ·
                  refine ⟨1356912566890336873313683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7236867023415129991006309 1356912566890336873313683)
                  ·
                    refine ⟨2035368850335505309970525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1356912566890336873313683 2035368850335505309970525)
                    ·
                      refine ⟨763263318875814491238947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2035368850335505309970525 763263318875814491238947)
                      ·
                        rfl

theorem cell23_1486450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 4, 1, 3].length) (baseStart_1486450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1486450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1486450 prefixEnd_1486450 := by exact prefixLift 1486450
  have htrace : WordTrace (prefixWord ++ tailWord_1486450) baseStart_1486450 baseEnd_1486450 := by
    simpa [prefixWord, tailWord_1486450, baseEnd_1486450] using wordTrace_append hprefix tailTrace_1486450
  have hstable : (prefixWord ++ tailWord_1486450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486450).length < 2 ^ (prefixWord ++ tailWord_1486450).sum := by decide
  have hdescent : baseEnd_1486450 < baseStart_1486450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486476 : List Nat := [2, 2, 1, 2, 1, 1, 3, 2, 1, 3, 5]
def baseStart_1486476 : Nat := 118140960795 + 1486476 * 2 ^ 59
def prefixEnd_1486476 : Nat := 4983230072969 + 3 ^ 40 * 1486476 * 2
def baseEnd_1486476 : Nat := 763276669372831389513827

theorem tailTrace_1486476 : CollatzResearch.WordTrace tailWord_1486476 prefixEnd_1486476 763276669372831389513827 := by
  unfold tailWord_1486476
  simp only [CollatzResearch.WordTrace]
  refine ⟨27108116881379398367147641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36144155841839197822863521 27108116881379398367147641)
  ·
    refine ⟨20331087661034548775360731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27108116881379398367147641 20331087661034548775360731)
    ·
      refine ⟨30496631491551823163041097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20331087661034548775360731 30496631491551823163041097)
      ·
        refine ⟨22872473618663867372280823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30496631491551823163041097 22872473618663867372280823)
        ·
          refine ⟨34308710427995801058421235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22872473618663867372280823 34308710427995801058421235)
          ·
            refine ⟨51463065641993701587631853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34308710427995801058421235 51463065641993701587631853)
            ·
              refine ⟨19298649615747638095361945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51463065641993701587631853 19298649615747638095361945)
              ·
                refine ⟨14473987211810728571521459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19298649615747638095361945 14473987211810728571521459)
                ·
                  refine ⟨21710980817716092857282189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14473987211810728571521459 21710980817716092857282189)
                  ·
                    refine ⟨8141617806643534821480821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21710980817716092857282189 8141617806643534821480821)
                    ·
                      refine ⟨763276669372831389513827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8141617806643534821480821 763276669372831389513827)
                      ·
                        rfl

theorem cell23_1486476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_1486476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1486476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1486476 prefixEnd_1486476 := by exact prefixLift 1486476
  have htrace : WordTrace (prefixWord ++ tailWord_1486476) baseStart_1486476 baseEnd_1486476 := by
    simpa [prefixWord, tailWord_1486476, baseEnd_1486476] using wordTrace_append hprefix tailTrace_1486476
  have hstable : (prefixWord ++ tailWord_1486476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486476).length < 2 ^ (prefixWord ++ tailWord_1486476).sum := by decide
  have hdescent : baseEnd_1486476 < baseStart_1486476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486484 : List Nat := [2, 4, 2, 2, 2, 1, 1, 3, 2, 1, 3]
def baseStart_1486484 : Nat := 118140960795 + 1486484 * 2 ^ 59
def prefixEnd_1486484 : Nat := 4983230072969 + 3 ^ 40 * 1486484 * 2
def baseEnd_1486484 : Nat := 763280777218067358213791

theorem tailTrace_1486484 : CollatzResearch.WordTrace tailWord_1486484 prefixEnd_1486484 763280777218067358213791 := by
  unfold tailWord_1486484
  simp only [CollatzResearch.WordTrace]
  refine ⟨27108262773364907050293253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36144350364486542733724337 27108262773364907050293253)
  ·
    refine ⟨5082799270005920071929985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27108262773364907050293253 5082799270005920071929985)
    ·
      refine ⟨3812099452504440053947489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5082799270005920071929985 3812099452504440053947489)
      ·
        refine ⟨2859074589378330040460617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3812099452504440053947489 2859074589378330040460617)
        ·
          refine ⟨2144305942033747530345463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2859074589378330040460617 2144305942033747530345463)
          ·
            refine ⟨3216458913050621295518195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2144305942033747530345463 3216458913050621295518195)
            ·
              refine ⟨4824688369575931943277293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3216458913050621295518195 4824688369575931943277293)
              ·
                refine ⟨1809258138590974478728985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4824688369575931943277293 1809258138590974478728985)
                ·
                  refine ⟨1356943603943230859046739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1809258138590974478728985 1356943603943230859046739)
                  ·
                    refine ⟨2035415405914846288570109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1356943603943230859046739 2035415405914846288570109)
                    ·
                      refine ⟨763280777218067358213791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2035415405914846288570109 763280777218067358213791)
                      ·
                        rfl

theorem cell23_1486484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_1486484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1486484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1486484 prefixEnd_1486484 := by exact prefixLift 1486484
  have htrace : WordTrace (prefixWord ++ tailWord_1486484) baseStart_1486484 baseEnd_1486484 := by
    simpa [prefixWord, tailWord_1486484, baseEnd_1486484] using wordTrace_append hprefix tailTrace_1486484
  have hstable : (prefixWord ++ tailWord_1486484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486484).length < 2 ^ (prefixWord ++ tailWord_1486484).sum := by decide
  have hdescent : baseEnd_1486484 < baseStart_1486484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486494 : List Nat := [4, 3, 1, 1, 1, 2, 3, 2, 1, 3, 2]
def baseStart_1486494 : Nat := 118140960795 + 1486494 * 2 ^ 59
def prefixEnd_1486494 : Nat := 4983230072969 + 3 ^ 40 * 1486494 * 2
def baseEnd_1486494 : Nat := 763285912024612319088745

theorem tailTrace_1486494 : CollatzResearch.WordTrace tailWord_1486494 prefixEnd_1486494 763285912024612319088745 := by
  unfold tailWord_1486494
  simp only [CollatzResearch.WordTrace]
  refine ⟨6777111284586698226056317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36144593517795723872300357 6777111284586698226056317)
  ·
    refine ⟨2541416731720011834771119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6777111284586698226056317 2541416731720011834771119)
    ·
      refine ⟨3812125097580017752156679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2541416731720011834771119 3812125097580017752156679)
      ·
        refine ⟨5718187646370026628235019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3812125097580017752156679 5718187646370026628235019)
        ·
          refine ⟨8577281469555039942352529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5718187646370026628235019 8577281469555039942352529)
          ·
            refine ⟨6432961102166279956764397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8577281469555039942352529 6432961102166279956764397)
            ·
              refine ⟨2412360413312354983786649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6432961102166279956764397 2412360413312354983786649)
              ·
                refine ⟨1809270309984266237839987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2412360413312354983786649 1809270309984266237839987)
                ·
                  refine ⟨2713905464976399356759981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1809270309984266237839987 2713905464976399356759981)
                  ·
                    refine ⟨1017714549366149758784993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2713905464976399356759981 1017714549366149758784993)
                    ·
                      refine ⟨763285912024612319088745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1017714549366149758784993 763285912024612319088745)
                      ·
                        rfl

theorem cell23_1486494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_1486494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1486494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1486494 prefixEnd_1486494 := by exact prefixLift 1486494
  have htrace : WordTrace (prefixWord ++ tailWord_1486494) baseStart_1486494 baseEnd_1486494 := by
    simpa [prefixWord, tailWord_1486494, baseEnd_1486494] using wordTrace_append hprefix tailTrace_1486494
  have hstable : (prefixWord ++ tailWord_1486494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486494).length < 2 ^ (prefixWord ++ tailWord_1486494).sum := by decide
  have hdescent : baseEnd_1486494 < baseStart_1486494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486524 : List Nat := [2, 2, 2, 3, 1, 3, 2, 2, 2, 2, 2]
def baseStart_1486524 : Nat := 118140960795 + 1486524 * 2 ^ 59
def prefixEnd_1486524 : Nat := 4983230072969 + 3 ^ 40 * 1486524 * 2
def baseEnd_1486524 : Nat := 763301316444247201713607

theorem tailTrace_1486524 : CollatzResearch.WordTrace tailWord_1486524 prefixEnd_1486524 763301316444247201713607 := by
  unfold tailWord_1486524
  simp only [CollatzResearch.WordTrace]
  refine ⟨27108992233292450466021313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36145322977723267288028417 27108992233292450466021313)
  ·
    refine ⟨20331744174969337849515985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27108992233292450466021313 20331744174969337849515985)
    ·
      refine ⟨15248808131227003387136989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20331744174969337849515985 15248808131227003387136989)
      ·
        refine ⟨5718303049210126270176371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15248808131227003387136989 5718303049210126270176371)
        ·
          refine ⟨8577454573815189405264557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5718303049210126270176371 8577454573815189405264557)
          ·
            refine ⟨3216545465180696026974209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8577454573815189405264557 3216545465180696026974209)
            ·
              refine ⟨2412409098885522020230657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3216545465180696026974209 2412409098885522020230657)
              ·
                refine ⟨1809306824164141515172993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2412409098885522020230657 1809306824164141515172993)
                ·
                  refine ⟨1356980118123106136379745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1809306824164141515172993 1356980118123106136379745)
                  ·
                    refine ⟨1017735088592329602284809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1356980118123106136379745 1017735088592329602284809)
                    ·
                      refine ⟨763301316444247201713607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1017735088592329602284809 763301316444247201713607)
                      ·
                        rfl

theorem cell23_1486524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_1486524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1486524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1486524 prefixEnd_1486524 := by exact prefixLift 1486524
  have htrace : WordTrace (prefixWord ++ tailWord_1486524) baseStart_1486524 baseEnd_1486524 := by
    simpa [prefixWord, tailWord_1486524, baseEnd_1486524] using wordTrace_append hprefix tailTrace_1486524
  have hstable : (prefixWord ++ tailWord_1486524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486524).length < 2 ^ (prefixWord ++ tailWord_1486524).sum := by decide
  have hdescent : baseEnd_1486524 < baseStart_1486524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486541 : List Nat := [1, 6, 2, 1, 1, 1, 2, 3, 2, 2, 2]
def baseStart_1486541 : Nat := 118140960795 + 1486541 * 2 ^ 59
def prefixEnd_1486541 : Nat := 4983230072969 + 3 ^ 40 * 1486541 * 2
def baseEnd_1486541 : Nat := 763310045615373635201029

theorem tailTrace_1486541 : CollatzResearch.WordTrace tailWord_1486541 prefixEnd_1486541 763310045615373635201029 := by
  unfold tailWord_1486541
  simp only [CollatzResearch.WordTrace]
  refine ⟨54218604507523312835411477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36145736338348875223607651 54218604507523312835411477)
  ·
    refine ⟨2541497086290155289159913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 54218604507523312835411477 2541497086290155289159913)
    ·
      refine ⟨1906122814717616466869935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2541497086290155289159913 1906122814717616466869935)
      ·
        refine ⟨2859184222076424700304903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1906122814717616466869935 2859184222076424700304903)
        ·
          refine ⟨4288776333114637050457355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2859184222076424700304903 4288776333114637050457355)
          ·
            refine ⟨6433164499671955575686033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4288776333114637050457355 6433164499671955575686033)
            ·
              refine ⟨4824873374753966681764525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6433164499671955575686033 4824873374753966681764525)
              ·
                refine ⟨1809327515532737505661697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4824873374753966681764525 1809327515532737505661697)
                ·
                  refine ⟨1356995636649553129246273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1809327515532737505661697 1356995636649553129246273)
                  ·
                    refine ⟨1017746727487164846934705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1356995636649553129246273 1017746727487164846934705)
                    ·
                      refine ⟨763310045615373635201029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1017746727487164846934705 763310045615373635201029)
                      ·
                        rfl

theorem cell23_1486541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_1486541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1486541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1486541 prefixEnd_1486541 := by exact prefixLift 1486541
  have htrace : WordTrace (prefixWord ++ tailWord_1486541) baseStart_1486541 baseEnd_1486541 := by
    simpa [prefixWord, tailWord_1486541, baseEnd_1486541] using wordTrace_append hprefix tailTrace_1486541
  have hstable : (prefixWord ++ tailWord_1486541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486541).length < 2 ^ (prefixWord ++ tailWord_1486541).sum := by decide
  have hdescent : baseEnd_1486541 < baseStart_1486541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486603 : List Nat := [1, 1, 1, 1, 5, 1, 2, 5, 6]
def baseStart_1486603 : Nat := 118140960795 + 1486603 * 2 ^ 59
def prefixEnd_1486603 : Nat := 4983230072969 + 3 ^ 40 * 1486603 * 2
def baseEnd_1486603 : Nat := 84815764601772488069527

theorem tailTrace_1486603 : CollatzResearch.WordTrace tailWord_1486603 prefixEnd_1486603 84815764601772488069527 := by
  unfold tailWord_1486603
  simp only [CollatzResearch.WordTrace]
  refine ⟨54220865833298697424168463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36147243888865798282778975 54220865833298697424168463)
  ·
    refine ⟨81331298749948046136252695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54220865833298697424168463 81331298749948046136252695)
    ·
      refine ⟨121996948124922069204379043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81331298749948046136252695 121996948124922069204379043)
      ·
        refine ⟨182995422187383103806568565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121996948124922069204379043 182995422187383103806568565)
        ·
          refine ⟨17155820830067165981865803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 182995422187383103806568565 17155820830067165981865803)
          ·
            refine ⟨25733731245100748972798705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17155820830067165981865803 25733731245100748972798705)
            ·
              refine ⟨19300298433825561729599029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25733731245100748972798705 19300298433825561729599029)
              ·
                refine ⟨1809402978171146412149909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19300298433825561729599029 1809402978171146412149909)
                ·
                  refine ⟨84815764601772488069527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1809402978171146412149909 84815764601772488069527)
                  ·
                    rfl

theorem cell23_1486603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 5, 6].length) (baseStart_1486603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1486603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1486603 prefixEnd_1486603 := by exact prefixLift 1486603
  have htrace : WordTrace (prefixWord ++ tailWord_1486603) baseStart_1486603 baseEnd_1486603 := by
    simpa [prefixWord, tailWord_1486603, baseEnd_1486603] using wordTrace_append hprefix tailTrace_1486603
  have hstable : (prefixWord ++ tailWord_1486603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486603).length < 2 ^ (prefixWord ++ tailWord_1486603).sum := by decide
  have hdescent : baseEnd_1486603 < baseStart_1486603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486654 : List Nat := [4, 2, 1, 2, 2, 3, 2, 1, 6]
def baseStart_1486654 : Nat := 118140960795 + 1486654 * 2 ^ 59
def prefixEnd_1486654 : Nat := 4983230072969 + 3 ^ 40 * 1486654 * 2
def baseEnd_1486654 : Nat := 84818674325481299232001

theorem tailTrace_1486654 : CollatzResearch.WordTrace tailWord_1486654 prefixEnd_1486654 84818674325481299232001 := by
  unfold tailWord_1486654
  simp only [CollatzResearch.WordTrace]
  refine ⟨6777840744514241641784377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36148483970742622089516677 6777840744514241641784377)
  ·
    refine ⟨5083380558385681231338283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6777840744514241641784377 5083380558385681231338283)
    ·
      refine ⟨7625070837578521847007425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5083380558385681231338283 7625070837578521847007425)
      ·
        refine ⟨5718803128183891385255569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7625070837578521847007425 5718803128183891385255569)
        ·
          refine ⟨4289102346137918538941677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5718803128183891385255569 4289102346137918538941677)
          ·
            refine ⟨1608413379801719452103129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4289102346137918538941677 1608413379801719452103129)
            ·
              refine ⟨1206310034851289589077347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1608413379801719452103129 1206310034851289589077347)
              ·
                refine ⟨1809465052276934383616021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1206310034851289589077347 1809465052276934383616021)
                ·
                  refine ⟨84818674325481299232001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1809465052276934383616021 84818674325481299232001)
                  ·
                    rfl

theorem cell23_1486654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 1, 6].length) (baseStart_1486654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1486654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1486654 prefixEnd_1486654 := by exact prefixLift 1486654
  have htrace : WordTrace (prefixWord ++ tailWord_1486654) baseStart_1486654 baseEnd_1486654 := by
    simpa [prefixWord, tailWord_1486654, baseEnd_1486654] using wordTrace_append hprefix tailTrace_1486654
  have hstable : (prefixWord ++ tailWord_1486654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486654).length < 2 ^ (prefixWord ++ tailWord_1486654).sum := by decide
  have hdescent : baseEnd_1486654 < baseStart_1486654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486674 : List Nat := [3, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2]
def baseStart_1486674 : Nat := 118140960795 + 1486674 * 2 ^ 59
def prefixEnd_1486674 : Nat := 4983230072969 + 3 ^ 40 * 1486674 * 2
def baseEnd_1486674 : Nat := 763378338542421614837917

theorem tailTrace_1486674 : CollatzResearch.WordTrace tailWord_1486674 prefixEnd_1486674 763378338542421614837917 := by
  unfold tailWord_1486674
  simp only [CollatzResearch.WordTrace]
  refine ⟨13555863854010369137500769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36148970277360984366668717 13555863854010369137500769)
  ·
    refine ⟨10166897890507776853125577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13555863854010369137500769 10166897890507776853125577)
    ·
      refine ⟨7625173417880832639844183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10166897890507776853125577 7625173417880832639844183)
      ·
        refine ⟨11437760126821248959766275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7625173417880832639844183 11437760126821248959766275)
        ·
          refine ⟨17156640190231873439649413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11437760126821248959766275 17156640190231873439649413)
          ·
            refine ⟨3216870035668476269934265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17156640190231873439649413 3216870035668476269934265)
            ·
              refine ⟨2412652526751357202450699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3216870035668476269934265 2412652526751357202450699)
              ·
                refine ⟨3618978790127035803676049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2412652526751357202450699 3618978790127035803676049)
                ·
                  refine ⟨2714234092595276852757037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3618978790127035803676049 2714234092595276852757037)
                  ·
                    refine ⟨1017837784723228819783889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2714234092595276852757037 1017837784723228819783889)
                    ·
                      refine ⟨763378338542421614837917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1017837784723228819783889 763378338542421614837917)
                      ·
                        rfl

theorem cell23_1486674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2].length) (baseStart_1486674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1486674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1486674 prefixEnd_1486674 := by exact prefixLift 1486674
  have htrace : WordTrace (prefixWord ++ tailWord_1486674) baseStart_1486674 baseEnd_1486674 := by
    simpa [prefixWord, tailWord_1486674, baseEnd_1486674] using wordTrace_append hprefix tailTrace_1486674
  have hstable : (prefixWord ++ tailWord_1486674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486674).length < 2 ^ (prefixWord ++ tailWord_1486674).sum := by decide
  have hdescent : baseEnd_1486674 < baseStart_1486674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486698 : List Nat := [3, 1, 3, 4, 1, 1, 1, 4, 1, 1, 3]
def baseStart_1486698 : Nat := 118140960795 + 1486698 * 2 ^ 59
def prefixEnd_1486698 : Nat := 4983230072969 + 3 ^ 40 * 1486698 * 2
def baseEnd_1486698 : Nat := 763390662078129520937807

theorem tailTrace_1486698 : CollatzResearch.WordTrace tailWord_1486698 prefixEnd_1486698 763390662078129520937807 := by
  unfold tailWord_1486698
  simp only [CollatzResearch.WordTrace]
  refine ⟨13556082691988632162219187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36149553845303019099251165 13556082691988632162219187)
  ·
    refine ⟨20334124037982948243328781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13556082691988632162219187 20334124037982948243328781)
    ·
      refine ⟨7625296514243605591248293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20334124037982948243328781 7625296514243605591248293)
      ·
        refine ⟨1429743096420676048359055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7625296514243605591248293 1429743096420676048359055)
        ·
          refine ⟨2144614644631014072538583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1429743096420676048359055 2144614644631014072538583)
          ·
            refine ⟨3216921966946521108807875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2144614644631014072538583 3216921966946521108807875)
            ·
              refine ⟨4825382950419781663211813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3216921966946521108807875 4825382950419781663211813)
              ·
                refine ⟨904759303203709061852215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4825382950419781663211813 904759303203709061852215)
                ·
                  refine ⟨1357138954805563592778323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 904759303203709061852215 1357138954805563592778323)
                  ·
                    refine ⟨2035708432208345389167485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1357138954805563592778323 2035708432208345389167485)
                    ·
                      refine ⟨763390662078129520937807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2035708432208345389167485 763390662078129520937807)
                      ·
                        rfl

theorem cell23_1486698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_1486698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1486698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1486698 prefixEnd_1486698 := by exact prefixLift 1486698
  have htrace : WordTrace (prefixWord ++ tailWord_1486698) baseStart_1486698 baseEnd_1486698 := by
    simpa [prefixWord, tailWord_1486698, baseEnd_1486698] using wordTrace_append hprefix tailTrace_1486698
  have hstable : (prefixWord ++ tailWord_1486698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486698).length < 2 ^ (prefixWord ++ tailWord_1486698).sum := by decide
  have hdescent : baseEnd_1486698 < baseStart_1486698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486727 : List Nat := [1, 1, 4, 2, 4, 1, 3, 7]
def baseStart_1486727 : Nat := 118140960795 + 1486727 * 2 ^ 59
def prefixEnd_1486727 : Nat := 4983230072969 + 3 ^ 40 * 1486727 * 2
def baseEnd_1486727 : Nat := 28274279741374441017599

theorem tailTrace_1486727 : CollatzResearch.WordTrace tailWord_1486727 prefixEnd_1486727 28274279741374441017599 := by
  unfold tailWord_1486727
  simp only [CollatzResearch.WordTrace]
  refine ⟨54225388484849466601682435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36150258989899644401121623 54225388484849466601682435)
  ·
    refine ⟨81338082727274199902523653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54225388484849466601682435 81338082727274199902523653)
    ·
      refine ⟨15250890511363912481723185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81338082727274199902523653 15250890511363912481723185)
      ·
        refine ⟨11438167883522934361292389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15250890511363912481723185 11438167883522934361292389)
        ·
          refine ⟨2144656478160550192742323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11438167883522934361292389 2144656478160550192742323)
          ·
            refine ⟨3216984717240825289113485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2144656478160550192742323 3216984717240825289113485)
            ·
              refine ⟨1206369268965309483417557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3216984717240825289113485 1206369268965309483417557)
              ·
                refine ⟨28274279741374441017599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1206369268965309483417557 28274279741374441017599)
                ·
                  rfl

theorem cell23_1486727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 7].length) (baseStart_1486727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1486727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1486727 prefixEnd_1486727 := by exact prefixLift 1486727
  have htrace : WordTrace (prefixWord ++ tailWord_1486727) baseStart_1486727 baseEnd_1486727 := by
    simpa [prefixWord, tailWord_1486727, baseEnd_1486727] using wordTrace_append hprefix tailTrace_1486727
  have hstable : (prefixWord ++ tailWord_1486727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486727).length < 2 ^ (prefixWord ++ tailWord_1486727).sum := by decide
  have hdescent : baseEnd_1486727 < baseStart_1486727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486738 : List Nat := [3, 2, 3, 2, 1, 1, 1, 5, 1, 2, 2]
def baseStart_1486738 : Nat := 118140960795 + 1486738 * 2 ^ 59
def prefixEnd_1486738 : Nat := 4983230072969 + 3 ^ 40 * 1486738 * 2
def baseEnd_1486738 : Nat := 763411201304309364437623

theorem tailTrace_1486738 : CollatzResearch.WordTrace tailWord_1486738 prefixEnd_1486738 763411201304309364437623 := by
  unfold tailWord_1486738
  simp only [CollatzResearch.WordTrace]
  refine ⟨13556447421952403870083217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36150526458539743653555245 13556447421952403870083217)
  ·
    refine ⟨10167335566464302902562413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13556447421952403870083217 10167335566464302902562413)
    ·
      refine ⟨3812750837424113588460905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10167335566464302902562413 3812750837424113588460905)
      ·
        refine ⟨2859563128068085191345679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3812750837424113588460905 2859563128068085191345679)
        ·
          refine ⟨4289344692102127787018519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2859563128068085191345679 4289344692102127787018519)
          ·
            refine ⟨6434017038153191680527779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4289344692102127787018519 6434017038153191680527779)
            ·
              refine ⟨9651025557229787520791669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6434017038153191680527779 9651025557229787520791669)
              ·
                refine ⟨904783645990292580074219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9651025557229787520791669 904783645990292580074219)
                ·
                  refine ⟨1357175468985438870111329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 904783645990292580074219 1357175468985438870111329)
                  ·
                    refine ⟨1017881601739079152583497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1357175468985438870111329 1017881601739079152583497)
                    ·
                      refine ⟨763411201304309364437623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1017881601739079152583497 763411201304309364437623)
                      ·
                        rfl

theorem cell23_1486738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_1486738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1486738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1486738 prefixEnd_1486738 := by exact prefixLift 1486738
  have htrace : WordTrace (prefixWord ++ tailWord_1486738) baseStart_1486738 baseEnd_1486738 := by
    simpa [prefixWord, tailWord_1486738, baseEnd_1486738] using wordTrace_append hprefix tailTrace_1486738
  have hstable : (prefixWord ++ tailWord_1486738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486738).length < 2 ^ (prefixWord ++ tailWord_1486738).sum := by decide
  have hdescent : baseEnd_1486738 < baseStart_1486738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486781 : List Nat := [1, 4, 1, 2, 3, 2, 2, 2, 1, 3, 2]
def baseStart_1486781 : Nat := 118140960795 + 1486781 * 2 ^ 59
def prefixEnd_1486781 : Nat := 4983230072969 + 3 ^ 40 * 1486781 * 2
def baseEnd_1486781 : Nat := 763433280972452696199925

theorem tailTrace_1486781 : CollatzResearch.WordTrace tailWord_1486781 prefixEnd_1486781 763433280972452696199925 := by
  unfold tailWord_1486781
  simp only [CollatzResearch.WordTrace]
  refine ⟨54227358026653833824148197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36151572017769222549432131 54227358026653833824148197)
  ·
    refine ⟨10167629629997593842027787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54227358026653833824148197 10167629629997593842027787)
    ·
      refine ⟨15251444444996390763041681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10167629629997593842027787 15251444444996390763041681)
      ·
        refine ⟨11438583333747293072281261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15251444444996390763041681 11438583333747293072281261)
        ·
          refine ⟨4289468750155234902105473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11438583333747293072281261 4289468750155234902105473)
          ·
            refine ⟨3217101562616426176579105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4289468750155234902105473 3217101562616426176579105)
            ·
              refine ⟨2412826171962319632434329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3217101562616426176579105 2412826171962319632434329)
              ·
                refine ⟨1809619628971739724325747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2412826171962319632434329 1809619628971739724325747)
                ·
                  refine ⟨2714429443457609586488621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1809619628971739724325747 2714429443457609586488621)
                  ·
                    refine ⟨1017911041296603594933233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2714429443457609586488621 1017911041296603594933233)
                    ·
                      refine ⟨763433280972452696199925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1017911041296603594933233 763433280972452696199925)
                      ·
                        rfl

theorem cell23_1486781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 2, 1, 3, 2].length) (baseStart_1486781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1486781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1486781 prefixEnd_1486781 := by exact prefixLift 1486781
  have htrace : WordTrace (prefixWord ++ tailWord_1486781) baseStart_1486781 baseEnd_1486781 := by
    simpa [prefixWord, tailWord_1486781, baseEnd_1486781] using wordTrace_append hprefix tailTrace_1486781
  have hstable : (prefixWord ++ tailWord_1486781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486781).length < 2 ^ (prefixWord ++ tailWord_1486781).sum := by decide
  have hdescent : baseEnd_1486781 < baseStart_1486781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486794 : List Nat := [3, 1, 2, 1, 2, 1, 3, 2, 4, 2, 2]
def baseStart_1486794 : Nat := 118140960795 + 1486794 * 2 ^ 59
def prefixEnd_1486794 : Nat := 4983230072969 + 3 ^ 40 * 1486794 * 2
def baseEnd_1486794 : Nat := 763439956220961145337365

theorem tailTrace_1486794 : CollatzResearch.WordTrace tailWord_1486794 prefixEnd_1486794 763439956220961145337365 := by
  unfold tailWord_1486794
  simp only [CollatzResearch.WordTrace]
  refine ⟨13556958043901684261092859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36151888117071158029580957 13556958043901684261092859)
  ·
    refine ⟨20335437065852526391639289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13556958043901684261092859 20335437065852526391639289)
    ·
      refine ⟨15251577799389394793729467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20335437065852526391639289 15251577799389394793729467)
      ·
        refine ⟨22877366699084092190594201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15251577799389394793729467 22877366699084092190594201)
        ·
          refine ⟨17158025024313069142945651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22877366699084092190594201 17158025024313069142945651)
          ·
            refine ⟨25737037536469603714418477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17158025024313069142945651 25737037536469603714418477)
            ·
              refine ⟨9651389076176101392906929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25737037536469603714418477 9651389076176101392906929)
              ·
                refine ⟨7238541807132076044680197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9651389076176101392906929 7238541807132076044680197)
                ·
                  refine ⟨1357226588837264258377537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7238541807132076044680197 1357226588837264258377537)
                  ·
                    refine ⟨1017919941627948193783153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1357226588837264258377537 1017919941627948193783153)
                    ·
                      refine ⟨763439956220961145337365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1017919941627948193783153 763439956220961145337365)
                      ·
                        rfl

theorem cell23_1486794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 4, 2, 2].length) (baseStart_1486794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1486794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1486794 prefixEnd_1486794 := by exact prefixLift 1486794
  have htrace : WordTrace (prefixWord ++ tailWord_1486794) baseStart_1486794 baseEnd_1486794 := by
    simpa [prefixWord, tailWord_1486794, baseEnd_1486794] using wordTrace_append hprefix tailTrace_1486794
  have hstable : (prefixWord ++ tailWord_1486794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486794).length < 2 ^ (prefixWord ++ tailWord_1486794).sum := by decide
  have hdescent : baseEnd_1486794 < baseStart_1486794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486817 : List Nat := [1, 2, 3, 1, 2, 1, 2, 6, 5]
def baseStart_1486817 : Nat := 118140960795 + 1486817 * 2 ^ 59
def prefixEnd_1486817 : Nat := 4983230072969 + 3 ^ 40 * 1486817 * 2
def baseEnd_1486817 : Nat := 84827974030668283927751

theorem tailTrace_1486817 : CollatzResearch.WordTrace tailWord_1486817 prefixEnd_1486817 84827974030668283927751 := by
  unfold tailWord_1486817
  simp only [CollatzResearch.WordTrace]
  refine ⟨54228671054523411972458705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36152447369682274648305803 54228671054523411972458705)
  ·
    refine ⟨40671503290892558979344029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54228671054523411972458705 40671503290892558979344029)
    ·
      refine ⟨15251813734084709617254011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40671503290892558979344029 15251813734084709617254011)
      ·
        refine ⟨22877720601127064425881017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15251813734084709617254011 22877720601127064425881017)
        ·
          refine ⟨17158290450845298319410763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22877720601127064425881017 17158290450845298319410763)
          ·
            refine ⟨25737435676267947479116145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17158290450845298319410763 25737435676267947479116145)
            ·
              refine ⟨19303076757200960609337109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25737435676267947479116145 19303076757200960609337109)
              ·
                refine ⟨904831722993795028562677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19303076757200960609337109 904831722993795028562677)
                ·
                  refine ⟨84827974030668283927751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 904831722993795028562677 84827974030668283927751)
                  ·
                    rfl

theorem cell23_1486817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 6, 5].length) (baseStart_1486817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1486817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1486817 prefixEnd_1486817 := by exact prefixLift 1486817
  have htrace : WordTrace (prefixWord ++ tailWord_1486817) baseStart_1486817 baseEnd_1486817 := by
    simpa [prefixWord, tailWord_1486817, baseEnd_1486817] using wordTrace_append hprefix tailTrace_1486817
  have hstable : (prefixWord ++ tailWord_1486817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486817).length < 2 ^ (prefixWord ++ tailWord_1486817).sum := by decide
  have hdescent : baseEnd_1486817 < baseStart_1486817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486867 : List Nat := [1, 1, 1, 2, 1, 4, 4, 2, 2, 1, 4]
def baseStart_1486867 : Nat := 118140960795 + 1486867 * 2 ^ 59
def prefixEnd_1486867 : Nat := 4983230072969 + 3 ^ 40 * 1486867 * 2
def baseEnd_1486867 : Nat := 763477440308739359724529

theorem tailTrace_1486867 : CollatzResearch.WordTrace tailWord_1486867 prefixEnd_1486867 763477440308739359724529 := by
  unfold tailWord_1486867
  simp only [CollatzResearch.WordTrace]
  refine ⟨54230494704342270511778855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36153663136228180341185903 54230494704342270511778855)
  ·
    refine ⟨81345742056513405767668283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54230494704342270511778855 81345742056513405767668283)
    ·
      refine ⟨122018613084770108651502425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81345742056513405767668283 122018613084770108651502425)
      ·
        refine ⟨91513959813577581488626819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122018613084770108651502425 91513959813577581488626819)
        ·
          refine ⟨137270939720366372232940229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91513959813577581488626819 137270939720366372232940229)
          ·
            refine ⟨25738301197568694793676293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137270939720366372232940229 25738301197568694793676293)
            ·
              refine ⟨4825931474544130273814305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25738301197568694793676293 4825931474544130273814305)
              ·
                refine ⟨3619448605908097705360729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4825931474544130273814305 3619448605908097705360729)
                ·
                  refine ⟨2714586454431073279020547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3619448605908097705360729 2714586454431073279020547)
                  ·
                    refine ⟨4071879681646609918530821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2714586454431073279020547 4071879681646609918530821)
                    ·
                      refine ⟨763477440308739359724529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4071879681646609918530821 763477440308739359724529)
                      ·
                        rfl

theorem cell23_1486867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2, 2, 1, 4].length) (baseStart_1486867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1486867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1486867 prefixEnd_1486867 := by exact prefixLift 1486867
  have htrace : WordTrace (prefixWord ++ tailWord_1486867) baseStart_1486867 baseEnd_1486867 := by
    simpa [prefixWord, tailWord_1486867, baseEnd_1486867] using wordTrace_append hprefix tailTrace_1486867
  have hstable : (prefixWord ++ tailWord_1486867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486867).length < 2 ^ (prefixWord ++ tailWord_1486867).sum := by decide
  have hdescent : baseEnd_1486867 < baseStart_1486867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486868 : List Nat := [2, 4, 3, 2, 1, 1, 1, 4, 5]
def baseStart_1486868 : Nat := 118140960795 + 1486868 * 2 ^ 59
def prefixEnd_1486868 : Nat := 4983230072969 + 3 ^ 40 * 1486868 * 2
def baseEnd_1486868 : Nat := 84830883754377095090225

theorem tailTrace_1486868 : CollatzResearch.WordTrace tailWord_1486868 prefixEnd_1486868 84830883754377095090225 := by
  unfold tailWord_1486868
  simp only [CollatzResearch.WordTrace]
  refine ⟨27115265588669323841282629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36153687451559098455043505 27115265588669323841282629)
  ·
    refine ⟨5084112297875498220240493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27115265588669323841282629 5084112297875498220240493)
    ·
      refine ⟨1906542111703311832590185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5084112297875498220240493 1906542111703311832590185)
      ·
        refine ⟨1429906583777483874442639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1906542111703311832590185 1429906583777483874442639)
        ·
          refine ⟨2144859875666225811663959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1429906583777483874442639 2144859875666225811663959)
          ·
            refine ⟨3217289813499338717495939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2144859875666225811663959 3217289813499338717495939)
            ·
              refine ⟨4825934720249008076243909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3217289813499338717495939 4825934720249008076243909)
              ·
                refine ⟨904862760046689014295733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4825934720249008076243909 904862760046689014295733)
                ·
                  refine ⟨84830883754377095090225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 904862760046689014295733 84830883754377095090225)
                  ·
                    rfl

theorem cell23_1486868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 4, 5].length) (baseStart_1486868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1486868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1486868 prefixEnd_1486868 := by exact prefixLift 1486868
  have htrace : WordTrace (prefixWord ++ tailWord_1486868) baseStart_1486868 baseEnd_1486868 := by
    simpa [prefixWord, tailWord_1486868, baseEnd_1486868] using wordTrace_append hprefix tailTrace_1486868
  have hstable : (prefixWord ++ tailWord_1486868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486868).length < 2 ^ (prefixWord ++ tailWord_1486868).sum := by decide
  have hdescent : baseEnd_1486868 < baseStart_1486868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486894 : List Nat := [4, 1, 3, 1, 1, 2, 1, 1, 5, 4]
def baseStart_1486894 : Nat := 118140960795 + 1486894 * 2 ^ 59
def prefixEnd_1486894 : Nat := 4983230072969 + 3 ^ 40 * 1486894 * 2
def baseEnd_1486894 : Nat := 254497101428803584695635

theorem tailTrace_1486894 : CollatzResearch.WordTrace tailWord_1486894 prefixEnd_1486894 254497101428803584695635 := by
  unfold tailWord_1486894
  simp only [CollatzResearch.WordTrace]
  refine ⟨6778934934405556765376467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36154319650162969415341157 6778934934405556765376467)
  ·
    refine ⟨10168402401608335148064701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6778934934405556765376467 10168402401608335148064701)
    ·
      refine ⟨3813150900603125680524263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10168402401608335148064701 3813150900603125680524263)
      ·
        refine ⟨5719726350904688520786395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3813150900603125680524263 5719726350904688520786395)
        ·
          refine ⟨8579589526357032781179593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5719726350904688520786395 8579589526357032781179593)
          ·
            refine ⟨6434692144767774585884695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8579589526357032781179593 6434692144767774585884695)
            ·
              refine ⟨9652038217151661878827043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6434692144767774585884695 9652038217151661878827043)
              ·
                refine ⟨14478057325727492818240565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9652038217151661878827043 14478057325727492818240565)
                ·
                  refine ⟨1357317874286952451710053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14478057325727492818240565 1357317874286952451710053)
                  ·
                    refine ⟨254497101428803584695635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1357317874286952451710053 254497101428803584695635)
                    ·
                      rfl

theorem cell23_1486894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_1486894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1486894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1486894 prefixEnd_1486894 := by exact prefixLift 1486894
  have htrace : WordTrace (prefixWord ++ tailWord_1486894) baseStart_1486894 baseEnd_1486894 := by
    simpa [prefixWord, tailWord_1486894, baseEnd_1486894] using wordTrace_append hprefix tailTrace_1486894
  have hstable : (prefixWord ++ tailWord_1486894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486894).length < 2 ^ (prefixWord ++ tailWord_1486894).sum := by decide
  have hdescent : baseEnd_1486894 < baseStart_1486894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486904 : List Nat := [2, 1, 2, 1, 6, 1, 1, 1, 1, 4, 3]
def baseStart_1486904 : Nat := 118140960795 + 1486904 * 2 ^ 59
def prefixEnd_1486904 : Nat := 4983230072969 + 3 ^ 40 * 1486904 * 2
def baseEnd_1486904 : Nat := 763496439092955714961859

theorem tailTrace_1486904 : CollatzResearch.WordTrace tailWord_1486904 prefixEnd_1486904 763496439092955714961859 := by
  unfold tailWord_1486904
  simp only [CollatzResearch.WordTrace]
  refine ⟨27115922102604112915437883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36154562803472150553917177 27115922102604112915437883)
  ·
    refine ⟨40673883153906169373156825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27115922102604112915437883 40673883153906169373156825)
    ·
      refine ⟨30505412365429627029867619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40673883153906169373156825 30505412365429627029867619)
      ·
        refine ⟨45758118548144440544801429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30505412365429627029867619 45758118548144440544801429)
        ·
          refine ⟨2144911806944270650537567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 45758118548144440544801429 2144911806944270650537567)
          ·
            refine ⟨3217367710416405975806351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2144911806944270650537567 3217367710416405975806351)
            ·
              refine ⟨4826051565624608963709527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3217367710416405975806351 4826051565624608963709527)
              ·
                refine ⟨7239077348436913445564291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4826051565624608963709527 7239077348436913445564291)
                ·
                  refine ⟨10858616022655370168346437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7239077348436913445564291 10858616022655370168346437)
                  ·
                    refine ⟨2035990504247881906564957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10858616022655370168346437 2035990504247881906564957)
                    ·
                      refine ⟨763496439092955714961859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2035990504247881906564957 763496439092955714961859)
                      ·
                        rfl

theorem cell23_1486904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 1, 4, 3].length) (baseStart_1486904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1486904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1486904 prefixEnd_1486904 := by exact prefixLift 1486904
  have htrace : WordTrace (prefixWord ++ tailWord_1486904) baseStart_1486904 baseEnd_1486904 := by
    simpa [prefixWord, tailWord_1486904, baseEnd_1486904] using wordTrace_append hprefix tailTrace_1486904
  have hstable : (prefixWord ++ tailWord_1486904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486904).length < 2 ^ (prefixWord ++ tailWord_1486904).sum := by decide
  have hdescent : baseEnd_1486904 < baseStart_1486904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486944 : List Nat := [2, 1, 1, 3, 2, 3, 1, 2, 1, 5, 2]
def baseStart_1486944 : Nat := 118140960795 + 1486944 * 2 ^ 59
def prefixEnd_1486944 : Nat := 4983230072969 + 3 ^ 40 * 1486944 * 2
def baseEnd_1486944 : Nat := 763516978319135558461675

theorem tailTrace_1486944 : CollatzResearch.WordTrace tailWord_1486944 prefixEnd_1486944 763516978319135558461675 := by
  unfold tailWord_1486944
  simp only [CollatzResearch.WordTrace]
  refine ⟨27116651562531656331165943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36155535416708875108221257 27116651562531656331165943)
  ·
    refine ⟨40674977343797484496748915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27116651562531656331165943 40674977343797484496748915)
    ·
      refine ⟨61012466015696226745123373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40674977343797484496748915 61012466015696226745123373)
      ·
        refine ⟨22879674755886085029421265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61012466015696226745123373 22879674755886085029421265)
        ·
          refine ⟨17159756066914563772065949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22879674755886085029421265 17159756066914563772065949)
          ·
            refine ⟨6434908525092961414524731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17159756066914563772065949 6434908525092961414524731)
            ·
              refine ⟨9652362787639442121787097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6434908525092961414524731 9652362787639442121787097)
              ·
                refine ⟨7239272090729581591340323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9652362787639442121787097 7239272090729581591340323)
                ·
                  refine ⟨10858908136094372387010485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7239272090729581591340323 10858908136094372387010485)
                  ·
                    refine ⟨1018022637758847411282233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10858908136094372387010485 1018022637758847411282233)
                    ·
                      refine ⟨763516978319135558461675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1018022637758847411282233 763516978319135558461675)
                      ·
                        rfl

theorem cell23_1486944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 1, 5, 2].length) (baseStart_1486944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1486944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1486944 prefixEnd_1486944 := by exact prefixLift 1486944
  have htrace : WordTrace (prefixWord ++ tailWord_1486944) baseStart_1486944 baseEnd_1486944 := by
    simpa [prefixWord, tailWord_1486944, baseEnd_1486944] using wordTrace_append hprefix tailTrace_1486944
  have hstable : (prefixWord ++ tailWord_1486944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486944).length < 2 ^ (prefixWord ++ tailWord_1486944).sum := by decide
  have hdescent : baseEnd_1486944 < baseStart_1486944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486994 : List Nat := [3, 2, 3, 1, 1, 1, 1, 4, 1, 1, 5]
def baseStart_1486994 : Nat := 118140960795 + 1486994 * 2 ^ 59
def prefixEnd_1486994 : Nat := 4983230072969 + 3 ^ 40 * 1486994 * 2
def baseEnd_1486994 : Nat := 763542652351860362836445

theorem tailTrace_1486994 : CollatzResearch.WordTrace tailWord_1486994 prefixEnd_1486994 763542652351860362836445 := by
  unfold tailWord_1486994
  simp only [CollatzResearch.WordTrace]
  refine ⟨13558781693720542800413009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36156751183254780801101357 13558781693720542800413009)
  ·
    refine ⟨10169086270290407100309757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13558781693720542800413009 10169086270290407100309757)
    ·
      refine ⟨3813407351358902662616159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10169086270290407100309757 3813407351358902662616159)
      ·
        refine ⟨5720111027038353993924239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3813407351358902662616159 5720111027038353993924239)
        ·
          refine ⟨8580166540557530990886359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5720111027038353993924239 8580166540557530990886359)
          ·
            refine ⟨12870249810836296486329539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8580166540557530990886359 12870249810836296486329539)
            ·
              refine ⟨19305374716254444729494309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12870249810836296486329539 19305374716254444729494309)
              ·
                refine ⟨3619757759297708386780183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19305374716254444729494309 3619757759297708386780183)
                ·
                  refine ⟨5429636638946562580170275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3619757759297708386780183 5429636638946562580170275)
                  ·
                    refine ⟨8144454958419843870255413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5429636638946562580170275 8144454958419843870255413)
                    ·
                      refine ⟨763542652351860362836445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8144454958419843870255413 763542652351860362836445)
                      ·
                        rfl

theorem cell23_1486994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_1486994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1486994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1486994 prefixEnd_1486994 := by exact prefixLift 1486994
  have htrace : WordTrace (prefixWord ++ tailWord_1486994) baseStart_1486994 baseEnd_1486994 := by
    simpa [prefixWord, tailWord_1486994, baseEnd_1486994] using wordTrace_append hprefix tailTrace_1486994
  have hstable : (prefixWord ++ tailWord_1486994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486994).length < 2 ^ (prefixWord ++ tailWord_1486994).sum := by decide
  have hdescent : baseEnd_1486994 < baseStart_1486994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486997 : List Nat := [1, 3, 2, 1, 1, 1, 6, 8]
def baseStart_1486997 : Nat := 118140960795 + 1486997 * 2 ^ 59
def prefixEnd_1486997 : Nat := 4983230072969 + 3 ^ 40 * 1486997 * 2
def baseEnd_1486997 : Nat := 28279414547919401892553

theorem tailTrace_1486997 : CollatzResearch.WordTrace tailWord_1486997 prefixEnd_1486997 28279414547919401892553 := by
  unfold tailWord_1486997
  simp only [CollatzResearch.WordTrace]
  refine ⟨54235236193871302714011245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36156824129247535142674163 54235236193871302714011245)
  ·
    refine ⟨20338213572701738517754217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54235236193871302714011245 20338213572701738517754217)
    ·
      refine ⟨15253660179526303888315663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20338213572701738517754217 15253660179526303888315663)
      ·
        refine ⟨22880490269289455832473495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15253660179526303888315663 22880490269289455832473495)
        ·
          refine ⟨34320735403934183748710243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22880490269289455832473495 34320735403934183748710243)
          ·
            refine ⟨51481103105901275623065365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34320735403934183748710243 51481103105901275623065365)
            ·
              refine ⟨2413176708089122294831189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 51481103105901275623065365 2413176708089122294831189)
              ·
                refine ⟨28279414547919401892553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2413176708089122294831189 28279414547919401892553)
                ·
                  rfl

theorem cell23_1486997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 8].length) (baseStart_1486997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1486997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1486997 prefixEnd_1486997 := by exact prefixLift 1486997
  have htrace : WordTrace (prefixWord ++ tailWord_1486997) baseStart_1486997 baseEnd_1486997 := by
    simpa [prefixWord, tailWord_1486997, baseEnd_1486997] using wordTrace_append hprefix tailTrace_1486997
  have hstable : (prefixWord ++ tailWord_1486997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486997).length < 2 ^ (prefixWord ++ tailWord_1486997).sum := by decide
  have hdescent : baseEnd_1486997 < baseStart_1486997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487004 : List Nat := [2, 2, 3, 2, 1, 1, 2, 3, 1, 2, 4]
def baseStart_1487004 : Nat := 118140960795 + 1487004 * 2 ^ 59
def prefixEnd_1487004 : Nat := 4983230072969 + 3 ^ 40 * 1487004 * 2
def baseEnd_1487004 : Nat := 763547787158405323711399

theorem tailTrace_1487004 : CollatzResearch.WordTrace tailWord_1487004 prefixEnd_1487004 763547787158405323711399 := by
  unfold tailWord_1487004
  simp only [CollatzResearch.WordTrace]
  refine ⟨27117745752422971454758033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36156994336563961939677377 27117745752422971454758033)
  ·
    refine ⟨20338309314317228591068525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27117745752422971454758033 20338309314317228591068525)
    ·
      refine ⟨7626865992868960721650697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20338309314317228591068525 7626865992868960721650697)
      ·
        refine ⟨5720149494651720541238023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7626865992868960721650697 5720149494651720541238023)
        ·
          refine ⟨8580224241977580811857035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5720149494651720541238023 8580224241977580811857035)
          ·
            refine ⟨12870336362966371217785553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8580224241977580811857035 12870336362966371217785553)
            ·
              refine ⟨9652752272224778413339165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12870336362966371217785553 9652752272224778413339165)
              ·
                refine ⟨3619782102084291905002187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9652752272224778413339165 3619782102084291905002187)
                ·
                  refine ⟨5429673153126437857503281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3619782102084291905002187 5429673153126437857503281)
                  ·
                    refine ⟨4072254864844828393127461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5429673153126437857503281 4072254864844828393127461)
                    ·
                      refine ⟨763547787158405323711399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4072254864844828393127461 763547787158405323711399)
                      ·
                        rfl

theorem cell23_1487004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_1487004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1487004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1487004 prefixEnd_1487004 := by exact prefixLift 1487004
  have htrace : WordTrace (prefixWord ++ tailWord_1487004) baseStart_1487004 baseEnd_1487004 := by
    simpa [prefixWord, tailWord_1487004, baseEnd_1487004] using wordTrace_append hprefix tailTrace_1487004
  have hstable : (prefixWord ++ tailWord_1487004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487004).length < 2 ^ (prefixWord ++ tailWord_1487004).sum := by decide
  have hdescent : baseEnd_1487004 < baseStart_1487004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487021 : List Nat := [1, 5, 2, 1, 2, 2, 1, 2, 1, 2, 4]
def baseStart_1487021 : Nat := 118140960795 + 1487021 * 2 ^ 59
def prefixEnd_1487021 : Nat := 4983230072969 + 3 ^ 40 * 1487021 * 2
def baseEnd_1487021 : Nat := 763556516329531757198821

theorem tailTrace_1487021 : CollatzResearch.WordTrace tailWord_1487021 prefixEnd_1487021 763556516329531757198821 := by
  unfold tailWord_1487021
  simp only [CollatzResearch.WordTrace]
  refine ⟨54236111545784354812884917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36157407697189569875256611 54236111545784354812884917)
  ·
    refine ⟨5084635457417283263707961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54236111545784354812884917 5084635457417283263707961)
    ·
      refine ⟨3813476593062962447780971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5084635457417283263707961 3813476593062962447780971)
      ·
        refine ⟨5720214889594443671671457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3813476593062962447780971 5720214889594443671671457)
        ·
          refine ⟨4290161167195832753753593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5720214889594443671671457 4290161167195832753753593)
          ·
            refine ⟨3217620875396874565315195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4290161167195832753753593 3217620875396874565315195)
            ·
              refine ⟨4826431313095311847972793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3217620875396874565315195 4826431313095311847972793)
              ·
                refine ⟨3619823484821483885979595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4826431313095311847972793 3619823484821483885979595)
                ·
                  refine ⟨5429735227232225828969393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3619823484821483885979595 5429735227232225828969393)
                  ·
                    refine ⟨4072301420424169371727045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5429735227232225828969393 4072301420424169371727045)
                    ·
                      refine ⟨763556516329531757198821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4072301420424169371727045 763556516329531757198821)
                      ·
                        rfl

theorem cell23_1487021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_1487021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1487021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1487021 prefixEnd_1487021 := by exact prefixLift 1487021
  have htrace : WordTrace (prefixWord ++ tailWord_1487021) baseStart_1487021 baseEnd_1487021 := by
    simpa [prefixWord, tailWord_1487021, baseEnd_1487021] using wordTrace_append hprefix tailTrace_1487021
  have hstable : (prefixWord ++ tailWord_1487021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487021).length < 2 ^ (prefixWord ++ tailWord_1487021).sum := by decide
  have hdescent : baseEnd_1487021 < baseStart_1487021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487044 : List Nat := [2, 3, 3, 1, 2, 1, 1, 1, 2, 7]
def baseStart_1487044 : Nat := 118140960795 + 1487044 * 2 ^ 59
def prefixEnd_1487044 : Nat := 4983230072969 + 3 ^ 40 * 1487044 * 2
def baseEnd_1487044 : Nat := 254522775461528389070405

theorem tailTrace_1487044 : CollatzResearch.WordTrace tailWord_1487044 prefixEnd_1487044 254522775461528389070405 := by
  unfold tailWord_1487044
  simp only [CollatzResearch.WordTrace]
  refine ⟨27118475212350514870486093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36157966949800686493981457 27118475212350514870486093)
  ·
    refine ⟨10169428204631443076432285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27118475212350514870486093 10169428204631443076432285)
    ·
      refine ⟨3813535576736791153662107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10169428204631443076432285 3813535576736791153662107)
      ·
        refine ⟨5720303365105186730493161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3813535576736791153662107 5720303365105186730493161)
        ·
          refine ⟨4290227523828890047869871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5720303365105186730493161 4290227523828890047869871)
          ·
            refine ⟨6435341285743335071804807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4290227523828890047869871 6435341285743335071804807)
            ·
              refine ⟨9653011928615002607707211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6435341285743335071804807 9653011928615002607707211)
              ·
                refine ⟨14479517892922503911560817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9653011928615002607707211 14479517892922503911560817)
                ·
                  refine ⟨10859638419691877933670613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14479517892922503911560817 10859638419691877933670613)
                  ·
                    refine ⟨254522775461528389070405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10859638419691877933670613 254522775461528389070405)
                    ·
                      rfl

theorem cell23_1487044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_1487044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1487044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1487044 prefixEnd_1487044 := by exact prefixLift 1487044
  have htrace : WordTrace (prefixWord ++ tailWord_1487044) baseStart_1487044 baseEnd_1487044 := by
    simpa [prefixWord, tailWord_1487044, baseEnd_1487044] using wordTrace_append hprefix tailTrace_1487044
  have hstable : (prefixWord ++ tailWord_1487044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487044).length < 2 ^ (prefixWord ++ tailWord_1487044).sum := by decide
  have hdescent : baseEnd_1487044 < baseStart_1487044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487057 : List Nat := [1, 2, 2, 1, 2, 2, 3, 1, 1, 8]
def baseStart_1487057 : Nat := 118140960795 + 1487057 * 2 ^ 59
def prefixEnd_1487057 : Nat := 4983230072969 + 3 ^ 40 * 1487057 * 2
def baseEnd_1487057 : Nat := 254525000544364538782885

theorem tailTrace_1487057 : CollatzResearch.WordTrace tailWord_1487057 prefixEnd_1487057 254525000544364538782885 := by
  unfold tailWord_1487057
  simp only [CollatzResearch.WordTrace]
  refine ⟨54237424573653932961195425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36158283049102621974130283 54237424573653932961195425)
  ·
    refine ⟨40678068430240449720896569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54237424573653932961195425 40678068430240449720896569)
    ·
      refine ⟨30508551322680337290672427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40678068430240449720896569 30508551322680337290672427)
      ·
        refine ⟨45762826984020505936008641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30508551322680337290672427 45762826984020505936008641)
        ·
          refine ⟨34322120238015379452006481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45762826984020505936008641 34322120238015379452006481)
          ·
            refine ⟨25741590178511534589004861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34322120238015379452006481 25741590178511534589004861)
            ·
              refine ⟨9653096316941825470876823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25741590178511534589004861 9653096316941825470876823)
              ·
                refine ⟨14479644475412738206315235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9653096316941825470876823 14479644475412738206315235)
                ·
                  refine ⟨21719466713119107309472853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14479644475412738206315235 21719466713119107309472853)
                  ·
                    refine ⟨254525000544364538782885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 21719466713119107309472853 254525000544364538782885)
                    ·
                      rfl

theorem cell23_1487057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 8].length) (baseStart_1487057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1487057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1487057 prefixEnd_1487057 := by exact prefixLift 1487057
  have htrace : WordTrace (prefixWord ++ tailWord_1487057) baseStart_1487057 baseEnd_1487057 := by
    simpa [prefixWord, tailWord_1487057, baseEnd_1487057] using wordTrace_append hprefix tailTrace_1487057
  have hstable : (prefixWord ++ tailWord_1487057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487057).length < 2 ^ (prefixWord ++ tailWord_1487057).sum := by decide
  have hdescent : baseEnd_1487057 < baseStart_1487057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487058 : List Nat := [3, 2, 2, 2, 1, 2, 2, 3, 2, 1, 3]
def baseStart_1487058 : Nat := 118140960795 + 1487058 * 2 ^ 59
def prefixEnd_1487058 : Nat := 4983230072969 + 3 ^ 40 * 1487058 * 2
def baseEnd_1487058 : Nat := 763575515113748112436151

theorem tailTrace_1487058 : CollatzResearch.WordTrace tailWord_1487058 prefixEnd_1487058 763575515113748112436151 := by
  unfold tailWord_1487058
  simp only [CollatzResearch.WordTrace]
  refine ⟨13559365261662577532995457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36158307364433540087987885 13559365261662577532995457)
  ·
    refine ⟨10169523946246933149746593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13559365261662577532995457 10169523946246933149746593)
    ·
      refine ⟨7627142959685199862309945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10169523946246933149746593 7627142959685199862309945)
      ·
        refine ⟨5720357219763899896732459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7627142959685199862309945 5720357219763899896732459)
        ·
          refine ⟨8580535829645849845098689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5720357219763899896732459 8580535829645849845098689)
          ·
            refine ⟨6435401872234387383824017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8580535829645849845098689 6435401872234387383824017)
            ·
              refine ⟨4826551404175790537868013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6435401872234387383824017 4826551404175790537868013)
              ·
                refine ⟨1809956776565921451700505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4826551404175790537868013 1809956776565921451700505)
                ·
                  refine ⟨1357467582424441088775379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1809956776565921451700505 1357467582424441088775379)
                  ·
                    refine ⟨2036201373636661633163069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1357467582424441088775379 2036201373636661633163069)
                    ·
                      refine ⟨763575515113748112436151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2036201373636661633163069 763575515113748112436151)
                      ·
                        rfl

theorem cell23_1487058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_1487058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1487058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1487058 prefixEnd_1487058 := by exact prefixLift 1487058
  have htrace : WordTrace (prefixWord ++ tailWord_1487058) baseStart_1487058 baseEnd_1487058 := by
    simpa [prefixWord, tailWord_1487058, baseEnd_1487058] using wordTrace_append hprefix tailTrace_1487058
  have hstable : (prefixWord ++ tailWord_1487058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487058).length < 2 ^ (prefixWord ++ tailWord_1487058).sum := by decide
  have hdescent : baseEnd_1487058 < baseStart_1487058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487081 : List Nat := [1, 2, 1, 1, 1, 2, 2, 3, 6, 2, 2]
def baseStart_1487081 : Nat := 118140960795 + 1487081 * 2 ^ 59
def prefixEnd_1487081 : Nat := 4983230072969 + 3 ^ 40 * 1487081 * 2
def baseEnd_1487081 : Nat := 763587325168801522448545

theorem tailTrace_1487081 : CollatzResearch.WordTrace tailWord_1487081 prefixEnd_1487081 763587325168801522448545 := by
  unfold tailWord_1487081
  simp only [CollatzResearch.WordTrace]
  refine ⟨54238299925566985060069097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36158866617044656706712731 54238299925566985060069097)
  ·
    refine ⟨40678724944175238795051823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54238299925566985060069097 40678724944175238795051823)
    ·
      refine ⟨61018087416262858192577735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40678724944175238795051823 61018087416262858192577735)
      ·
        refine ⟨91527131124394287288866603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61018087416262858192577735 91527131124394287288866603)
        ·
          refine ⟨137290696686591430933299905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91527131124394287288866603 137290696686591430933299905)
          ·
            refine ⟨102968022514943573199974929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137290696686591430933299905 102968022514943573199974929)
            ·
              refine ⟨77226016886207679899981197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102968022514943573199974929 77226016886207679899981197)
              ·
                refine ⟨28959756332327879962492949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77226016886207679899981197 28959756332327879962492949)
                ·
                  refine ⟨1357488578077869373241857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 28959756332327879962492949 1357488578077869373241857)
                  ·
                    refine ⟨1018116433558402029931393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1357488578077869373241857 1018116433558402029931393)
                    ·
                      refine ⟨763587325168801522448545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1018116433558402029931393 763587325168801522448545)
                      ·
                        rfl

theorem cell23_1487081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 6, 2, 2].length) (baseStart_1487081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1487081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1487081 prefixEnd_1487081 := by exact prefixLift 1487081
  have htrace : WordTrace (prefixWord ++ tailWord_1487081) baseStart_1487081 baseEnd_1487081 := by
    simpa [prefixWord, tailWord_1487081, baseEnd_1487081] using wordTrace_append hprefix tailTrace_1487081
  have hstable : (prefixWord ++ tailWord_1487081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487081).length < 2 ^ (prefixWord ++ tailWord_1487081).sum := by decide
  have hdescent : baseEnd_1487081 < baseStart_1487081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487085 : List Nat := [1, 5, 1, 2, 3, 1, 1, 3, 1, 3, 2]
def baseStart_1487085 : Nat := 118140960795 + 1487085 * 2 ^ 59
def prefixEnd_1487085 : Nat := 4983230072969 + 3 ^ 40 * 1487085 * 2
def baseEnd_1487085 : Nat := 763589379091419506798527

theorem tailTrace_1487085 : CollatzResearch.WordTrace tailWord_1487085 prefixEnd_1487085 763589379091419506798527 := by
  unfold tailWord_1487085
  simp only [CollatzResearch.WordTrace]
  refine ⟨54238445817552493743214709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36158963878368329162143139 54238445817552493743214709)
  ·
    refine ⟨5084854295395546288426379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54238445817552493743214709 5084854295395546288426379)
    ·
      refine ⟨7627281443093319432639569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5084854295395546288426379 7627281443093319432639569)
      ·
        refine ⟨5720461082319989574479677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7627281443093319432639569 5720461082319989574479677)
        ·
          refine ⟨2145172905869996090429879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5720461082319989574479677 2145172905869996090429879)
          ·
            refine ⟨3217759358804994135644819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2145172905869996090429879 3217759358804994135644819)
            ·
              refine ⟨4826639038207491203467229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3217759358804994135644819 4826639038207491203467229)
              ·
                refine ⟨1809989639327809201300211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4826639038207491203467229 1809989639327809201300211)
                ·
                  refine ⟨2714984458991713801950317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1809989639327809201300211 2714984458991713801950317)
                  ·
                    refine ⟨1018119172121892675731369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2714984458991713801950317 1018119172121892675731369)
                    ·
                      refine ⟨763589379091419506798527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1018119172121892675731369 763589379091419506798527)
                      ·
                        rfl

theorem cell23_1487085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_1487085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1487085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1487085 prefixEnd_1487085 := by exact prefixLift 1487085
  have htrace : WordTrace (prefixWord ++ tailWord_1487085) baseStart_1487085 baseEnd_1487085 := by
    simpa [prefixWord, tailWord_1487085, baseEnd_1487085] using wordTrace_append hprefix tailTrace_1487085
  have hstable : (prefixWord ++ tailWord_1487085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487085).length < 2 ^ (prefixWord ++ tailWord_1487085).sum := by decide
  have hdescent : baseEnd_1487085 < baseStart_1487085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487097 : List Nat := [1, 2, 1, 3, 1, 1, 2, 1, 1, 1, 9]
def baseStart_1487097 : Nat := 118140960795 + 1487097 * 2 ^ 59
def prefixEnd_1487097 : Nat := 4983230072969 + 3 ^ 40 * 1487097 * 2
def baseEnd_1487097 : Nat := 763595540859273459848471

theorem tailTrace_1487097 : CollatzResearch.WordTrace tailWord_1487097 prefixEnd_1487097 763595540859273459848471 := by
  unfold tailWord_1487097
  simp only [CollatzResearch.WordTrace]
  refine ⟨54238883493509019792651545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36159255662339346528434363 54238883493509019792651545)
  ·
    refine ⟨40679162620131764844488659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54238883493509019792651545 40679162620131764844488659)
    ·
      refine ⟨61018743930197647266732989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40679162620131764844488659 61018743930197647266732989)
      ·
        refine ⟨22882028973824117725024871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61018743930197647266732989 22882028973824117725024871)
        ·
          refine ⟨34323043460736176587537307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22882028973824117725024871 34323043460736176587537307)
          ·
            refine ⟨51484565191104264881305961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34323043460736176587537307 51484565191104264881305961)
            ·
              refine ⟨38613423893328198660979471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51484565191104264881305961 38613423893328198660979471)
              ·
                refine ⟨57920135839992297991469207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38613423893328198660979471 57920135839992297991469207)
                ·
                  refine ⟨86880203759988446987203811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57920135839992297991469207 86880203759988446987203811)
                  ·
                    refine ⟨130320305639982670480805717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 86880203759988446987203811 130320305639982670480805717)
                    ·
                      refine ⟨763595540859273459848471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 130320305639982670480805717 763595540859273459848471)
                      ·
                        rfl

theorem cell23_1487097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_1487097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1487097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1487097 prefixEnd_1487097 := by exact prefixLift 1487097
  have htrace : WordTrace (prefixWord ++ tailWord_1487097) baseStart_1487097 baseEnd_1487097 := by
    simpa [prefixWord, tailWord_1487097, baseEnd_1487097] using wordTrace_append hprefix tailTrace_1487097
  have hstable : (prefixWord ++ tailWord_1487097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487097).length < 2 ^ (prefixWord ++ tailWord_1487097).sum := by decide
  have hdescent : baseEnd_1487097 < baseStart_1487097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487098 : List Nat := [3, 1, 1, 1, 1, 6, 1, 1, 4, 2, 2]
def baseStart_1487098 : Nat := 118140960795 + 1487098 * 2 ^ 59
def prefixEnd_1487098 : Nat := 4983230072969 + 3 ^ 40 * 1487098 * 2
def baseEnd_1487098 : Nat := 763596054339927955935967

theorem tailTrace_1487098 : CollatzResearch.WordTrace tailWord_1487098 prefixEnd_1487098 763596054339927955935967 := by
  unfold tailWord_1487098
  simp only [CollatzResearch.WordTrace]
  refine ⟨13559729991626349240859487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36159279977670264642291965 13559729991626349240859487)
  ·
    refine ⟨20339594987439523861289231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13559729991626349240859487 20339594987439523861289231)
    ·
      refine ⟨30509392481159285791933847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20339594987439523861289231 30509392481159285791933847)
      ·
        refine ⟨45764088721738928687900771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30509392481159285791933847 45764088721738928687900771)
        ·
          refine ⟨68646133082608393031851157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45764088721738928687900771 68646133082608393031851157)
          ·
            refine ⟨3217787488247268423368023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 68646133082608393031851157 3217787488247268423368023)
            ·
              refine ⟨4826681232370902635052035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3217787488247268423368023 4826681232370902635052035)
              ·
                refine ⟨7240021848556353952578053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4826681232370902635052035 7240021848556353952578053)
                ·
                  refine ⟨1357504096604316366108385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7240021848556353952578053 1357504096604316366108385)
                  ·
                    refine ⟨1018128072453237274581289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1357504096604316366108385 1018128072453237274581289)
                    ·
                      refine ⟨763596054339927955935967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1018128072453237274581289 763596054339927955935967)
                      ·
                        rfl

theorem cell23_1487098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 4, 2, 2].length) (baseStart_1487098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1487098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1487098 prefixEnd_1487098 := by exact prefixLift 1487098
  have htrace : WordTrace (prefixWord ++ tailWord_1487098) baseStart_1487098 baseEnd_1487098 := by
    simpa [prefixWord, tailWord_1487098, baseEnd_1487098] using wordTrace_append hprefix tailTrace_1487098
  have hstable : (prefixWord ++ tailWord_1487098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487098).length < 2 ^ (prefixWord ++ tailWord_1487098).sum := by decide
  have hdescent : baseEnd_1487098 < baseStart_1487098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487115 : List Nat := [1, 1, 1, 1, 5, 2, 5, 1, 2, 2, 2]
def baseStart_1487115 : Nat := 118140960795 + 1487115 * 2 ^ 59
def prefixEnd_1487115 : Nat := 4983230072969 + 3 ^ 40 * 1487115 * 2
def baseEnd_1487115 : Nat := 763604783511054389423389

theorem tailTrace_1487115 : CollatzResearch.WordTrace tailWord_1487115 prefixEnd_1487115 763604783511054389423389 := by
  unfold tailWord_1487115
  simp only [CollatzResearch.WordTrace]
  refine ⟨54239540007443808866806799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36159693338295872577871199 54239540007443808866806799)
  ·
    refine ⟨81359310011165713300210199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54239540007443808866806799 81359310011165713300210199)
    ·
      refine ⟨122038965016748569950315299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81359310011165713300210199 122038965016748569950315299)
      ·
        refine ⟨183058447525122854925472949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122038965016748569950315299 183058447525122854925472949)
        ·
          refine ⟨17161729455480267649263089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 183058447525122854925472949 17161729455480267649263089)
          ·
            refine ⟨12871297091610200736947317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17161729455480267649263089 12871297091610200736947317)
            ·
              refine ⟨1206684102338456319088811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12871297091610200736947317 1206684102338456319088811)
              ·
                refine ⟨1810026153507684478633217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1206684102338456319088811 1810026153507684478633217)
                ·
                  refine ⟨1357519615130763358974913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1810026153507684478633217 1357519615130763358974913)
                  ·
                    refine ⟨1018139711348072519231185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1357519615130763358974913 1018139711348072519231185)
                    ·
                      refine ⟨763604783511054389423389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1018139711348072519231185 763604783511054389423389)
                      ·
                        rfl

theorem cell23_1487115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 1, 2, 2, 2].length) (baseStart_1487115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1487115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1487115 prefixEnd_1487115 := by exact prefixLift 1487115
  have htrace : WordTrace (prefixWord ++ tailWord_1487115) baseStart_1487115 baseEnd_1487115 := by
    simpa [prefixWord, tailWord_1487115, baseEnd_1487115] using wordTrace_append hprefix tailTrace_1487115
  have hstable : (prefixWord ++ tailWord_1487115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487115).length < 2 ^ (prefixWord ++ tailWord_1487115).sum := by decide
  have hdescent : baseEnd_1487115 < baseStart_1487115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487138 : List Nat := [3, 3, 1, 1, 3, 1, 3, 3, 5]
def baseStart_1487138 : Nat := 118140960795 + 1487138 * 2 ^ 59
def prefixEnd_1487138 : Nat := 4983230072969 + 3 ^ 40 * 1487138 * 2
def baseEnd_1487138 : Nat := 84846288174011977715087

theorem tailTrace_1487138 : CollatzResearch.WordTrace tailWord_1487138 prefixEnd_1487138 84846288174011977715087 := by
  unfold tailWord_1487138
  simp only [CollatzResearch.WordTrace]
  refine ⟨13560094721590120948723517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36160252590906989196596045 13560094721590120948723517)
  ·
    refine ⟨5085035520596295355771319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13560094721590120948723517 5085035520596295355771319)
    ·
      refine ⟨7627553280894443033656979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5085035520596295355771319 7627553280894443033656979)
      ·
        refine ⟨11441329921341664550485469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7627553280894443033656979 11441329921341664550485469)
        ·
          refine ⟨4290498720503124206432051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11441329921341664550485469 4290498720503124206432051)
          ·
            refine ⟨6435748080754686309648077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4290498720503124206432051 6435748080754686309648077)
            ·
              refine ⟨2413405530283007366118029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6435748080754686309648077 2413405530283007366118029)
              ·
                refine ⟨905027073856127762294261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2413405530283007366118029 905027073856127762294261)
                ·
                  refine ⟨84846288174011977715087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 905027073856127762294261 84846288174011977715087)
                  ·
                    rfl

theorem cell23_1487138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 3, 5].length) (baseStart_1487138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1487138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1487138 prefixEnd_1487138 := by exact prefixLift 1487138
  have htrace : WordTrace (prefixWord ++ tailWord_1487138) baseStart_1487138 baseEnd_1487138 := by
    simpa [prefixWord, tailWord_1487138, baseEnd_1487138] using wordTrace_append hprefix tailTrace_1487138
  have hstable : (prefixWord ++ tailWord_1487138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487138).length < 2 ^ (prefixWord ++ tailWord_1487138).sum := by decide
  have hdescent : baseEnd_1487138 < baseStart_1487138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487161 : List Nat := [1, 2, 1, 6, 1, 2, 1, 1, 1, 2, 5]
def baseStart_1487161 : Nat := 118140960795 + 1487161 * 2 ^ 59
def prefixEnd_1487161 : Nat := 4983230072969 + 3 ^ 40 * 1487161 * 2
def baseEnd_1487161 : Nat := 763628403621161209448177

theorem tailTrace_1487161 : CollatzResearch.WordTrace tailWord_1487161 prefixEnd_1487161 763628403621161209448177 := by
  unfold tailWord_1487161
  simp only [CollatzResearch.WordTrace]
  refine ⟨54241217765277158722981337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36160811843518105815320891 54241217765277158722981337)
  ·
    refine ⟨40680913323957869042236003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54241217765277158722981337 40680913323957869042236003)
    ·
      refine ⟨61021369985936803563354005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40680913323957869042236003 61021369985936803563354005)
      ·
        refine ⟨2860376718090787667032219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 61021369985936803563354005 2860376718090787667032219)
        ·
          refine ⟨4290565077136181500548329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2860376718090787667032219 4290565077136181500548329)
          ·
            refine ⟨3217923807852136125411247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4290565077136181500548329 3217923807852136125411247)
            ·
              refine ⟨4826885711778204188116871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3217923807852136125411247 4826885711778204188116871)
              ·
                refine ⟨7240328567667306282175307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4826885711778204188116871 7240328567667306282175307)
                ·
                  refine ⟨10860492851500959423262961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7240328567667306282175307 10860492851500959423262961)
                  ·
                    refine ⟨8145369638625719567447221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10860492851500959423262961 8145369638625719567447221)
                    ·
                      refine ⟨763628403621161209448177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8145369638625719567447221 763628403621161209448177)
                      ·
                        rfl

theorem cell23_1487161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_1487161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1487161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1487161 prefixEnd_1487161 := by exact prefixLift 1487161
  have htrace : WordTrace (prefixWord ++ tailWord_1487161) baseStart_1487161 baseEnd_1487161 := by
    simpa [prefixWord, tailWord_1487161, baseEnd_1487161] using wordTrace_append hprefix tailTrace_1487161
  have hstable : (prefixWord ++ tailWord_1487161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487161).length < 2 ^ (prefixWord ++ tailWord_1487161).sum := by decide
  have hdescent : baseEnd_1487161 < baseStart_1487161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487171 : List Nat := [1, 1, 1, 3, 1, 3, 2, 3, 2, 4, 2]
def baseStart_1487171 : Nat := 118140960795 + 1487171 * 2 ^ 59
def prefixEnd_1487171 : Nat := 4983230072969 + 3 ^ 40 * 1487171 * 2
def baseEnd_1487171 : Nat := 763633538427706170323131

theorem tailTrace_1487171 : CollatzResearch.WordTrace tailWord_1487171 prefixEnd_1487171 763633538427706170323131 := by
  unfold tailWord_1487171
  simp only [CollatzResearch.WordTrace]
  refine ⟨54241582495240930430845367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36161054996827286953896911 54241582495240930430845367)
  ·
    refine ⟨81362373742861395646268051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54241582495240930430845367 81362373742861395646268051)
    ·
      refine ⟨122043560614292093469402077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81362373742861395646268051 122043560614292093469402077)
      ·
        refine ⟨45766335230359535051025779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122043560614292093469402077 45766335230359535051025779)
        ·
          refine ⟨68649502845539302576538669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45766335230359535051025779 68649502845539302576538669)
          ·
            refine ⟨25743563567077238466202001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68649502845539302576538669 25743563567077238466202001)
            ·
              refine ⟨19307672675307928849651501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25743563567077238466202001 19307672675307928849651501)
              ·
                refine ⟨7240377253240473318619313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19307672675307928849651501 7240377253240473318619313)
                ·
                  refine ⟨5430282939930354988964485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7240377253240473318619313 5430282939930354988964485)
                  ·
                    refine ⟨1018178051236941560430841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5430282939930354988964485 1018178051236941560430841)
                    ·
                      refine ⟨763633538427706170323131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1018178051236941560430841 763633538427706170323131)
                      ·
                        rfl

theorem cell23_1487171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 4, 2].length) (baseStart_1487171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1487171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1487171 prefixEnd_1487171 := by exact prefixLift 1487171
  have htrace : WordTrace (prefixWord ++ tailWord_1487171) baseStart_1487171 baseEnd_1487171 := by
    simpa [prefixWord, tailWord_1487171, baseEnd_1487171] using wordTrace_append hprefix tailTrace_1487171
  have hstable : (prefixWord ++ tailWord_1487171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487171).length < 2 ^ (prefixWord ++ tailWord_1487171).sum := by decide
  have hdescent : baseEnd_1487171 < baseStart_1487171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487188 : List Nat := [2, 4, 1, 1, 2, 3, 2, 1, 2, 1, 4]
def baseStart_1487188 : Nat := 118140960795 + 1487188 * 2 ^ 59
def prefixEnd_1487188 : Nat := 4983230072969 + 3 ^ 40 * 1487188 * 2
def baseEnd_1487188 : Nat := 763642267598832603810553

theorem tailTrace_1487188 : CollatzResearch.WordTrace tailWord_1487188 prefixEnd_1487188 763642267598832603810553 := by
  unfold tailWord_1487188
  simp only [CollatzResearch.WordTrace]
  refine ⟨27121101268089671167107109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36161468357452894889476145 27121101268089671167107109)
  ·
    refine ⟨5085206487766813343832583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27121101268089671167107109 5085206487766813343832583)
    ·
      refine ⟨7627809731650220015748875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5085206487766813343832583 7627809731650220015748875)
      ·
        refine ⟨11441714597475330023623313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7627809731650220015748875 11441714597475330023623313)
        ·
          refine ⟨8581285948106497517717485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11441714597475330023623313 8581285948106497517717485)
          ·
            refine ⟨3217982230539936569144057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8581285948106497517717485 3217982230539936569144057)
            ·
              refine ⟨2413486672904952426858043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3217982230539936569144057 2413486672904952426858043)
              ·
                refine ⟨3620230009357428640287065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2413486672904952426858043 3620230009357428640287065)
                ·
                  refine ⟨2715172507018071480215299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3620230009357428640287065 2715172507018071480215299)
                  ·
                    refine ⟨4072758760527107220322949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2715172507018071480215299 4072758760527107220322949)
                    ·
                      refine ⟨763642267598832603810553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4072758760527107220322949 763642267598832603810553)
                      ·
                        rfl

theorem cell23_1487188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_1487188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1487188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1487188 prefixEnd_1487188 := by exact prefixLift 1487188
  have htrace : WordTrace (prefixWord ++ tailWord_1487188) baseStart_1487188 baseEnd_1487188 := by
    simpa [prefixWord, tailWord_1487188, baseEnd_1487188] using wordTrace_append hprefix tailTrace_1487188
  have hstable : (prefixWord ++ tailWord_1487188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487188).length < 2 ^ (prefixWord ++ tailWord_1487188).sum := by decide
  have hdescent : baseEnd_1487188 < baseStart_1487188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487208 : List Nat := [2, 1, 4, 2, 2, 1, 2, 2, 2, 2, 3]
def baseStart_1487208 : Nat := 118140960795 + 1487208 * 2 ^ 59
def prefixEnd_1487208 : Nat := 4983230072969 + 3 ^ 40 * 1487208 * 2
def baseEnd_1487208 : Nat := 763652537211922525560461

theorem tailTrace_1487208 : CollatzResearch.WordTrace tailWord_1487208 prefixEnd_1487208 763652537211922525560461 := by
  unfold tailWord_1487208
  simp only [CollatzResearch.WordTrace]
  refine ⟨27121465998053442874971139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36161954664071257166628185 27121465998053442874971139)
  ·
    refine ⟨40682198997080164312456709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27121465998053442874971139 40682198997080164312456709)
    ·
      refine ⟨7627912311952530808585633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40682198997080164312456709 7627912311952530808585633)
      ·
        refine ⟨5720934233964398106439225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7627912311952530808585633 5720934233964398106439225)
        ·
          refine ⟨4290700675473298579829419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5720934233964398106439225 4290700675473298579829419)
          ·
            refine ⟨6436051013209947869744129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4290700675473298579829419 6436051013209947869744129)
            ·
              refine ⟨4827038259907460902308097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6436051013209947869744129 4827038259907460902308097)
              ·
                refine ⟨3620278694930595676731073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4827038259907460902308097 3620278694930595676731073)
                ·
                  refine ⟨2715209021197946757548305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3620278694930595676731073 2715209021197946757548305)
                  ·
                    refine ⟨2036406765898460068161229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2715209021197946757548305 2036406765898460068161229)
                    ·
                      refine ⟨763652537211922525560461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2036406765898460068161229 763652537211922525560461)
                      ·
                        rfl

theorem cell23_1487208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_1487208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1487208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1487208 prefixEnd_1487208 := by exact prefixLift 1487208
  have htrace : WordTrace (prefixWord ++ tailWord_1487208) baseStart_1487208 baseEnd_1487208 := by
    simpa [prefixWord, tailWord_1487208, baseEnd_1487208] using wordTrace_append hprefix tailTrace_1487208
  have hstable : (prefixWord ++ tailWord_1487208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487208).length < 2 ^ (prefixWord ++ tailWord_1487208).sum := by decide
  have hdescent : baseEnd_1487208 < baseStart_1487208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487222 : List Nat := [5, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2]
def baseStart_1487222 : Nat := 118140960795 + 1487222 * 2 ^ 59
def prefixEnd_1487222 : Nat := 4983230072969 + 3 ^ 40 * 1487222 * 2
def baseEnd_1487222 : Nat := 763659725941085470785397

theorem tailTrace_1487222 : CollatzResearch.WordTrace tailWord_1487222 prefixEnd_1487222 763659725941085470785397 := by
  unfold tailWord_1487222
  simp only [CollatzResearch.WordTrace]
  refine ⟨3390215163628510383809495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36162295078704110760634613 3390215163628510383809495)
  ·
    refine ⟨5085322745442765575714243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3390215163628510383809495 5085322745442765575714243)
    ·
      refine ⟨7627984118164148363571365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5085322745442765575714243 7627984118164148363571365)
      ·
        refine ⟨1430247022155777818169631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7627984118164148363571365 1430247022155777818169631)
        ·
          refine ⟨2145370533233666727254447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1430247022155777818169631 2145370533233666727254447)
          ·
            refine ⟨3218055799850500090881671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2145370533233666727254447 3218055799850500090881671)
            ·
              refine ⟨4827083699775750136322507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3218055799850500090881671 4827083699775750136322507)
              ·
                refine ⟨7240625549663625204483761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4827083699775750136322507 7240625549663625204483761)
                ·
                  refine ⟨5430469162247718903362821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7240625549663625204483761 5430469162247718903362821)
                  ·
                    refine ⟨1018212967921447294380529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5430469162247718903362821 1018212967921447294380529)
                    ·
                      refine ⟨763659725941085470785397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1018212967921447294380529 763659725941085470785397)
                      ·
                        rfl

theorem cell23_1487222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_1487222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1487222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1487222 prefixEnd_1487222 := by exact prefixLift 1487222
  have htrace : WordTrace (prefixWord ++ tailWord_1487222) baseStart_1487222 baseEnd_1487222 := by
    simpa [prefixWord, tailWord_1487222, baseEnd_1487222] using wordTrace_append hprefix tailTrace_1487222
  have hstable : (prefixWord ++ tailWord_1487222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487222).length < 2 ^ (prefixWord ++ tailWord_1487222).sum := by decide
  have hdescent : baseEnd_1487222 < baseStart_1487222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487231 : List Nat := [1, 1, 2, 2, 1, 1, 2, 3, 3, 5, 2]
def baseStart_1487231 : Nat := 118140960795 + 1487231 * 2 ^ 59
def prefixEnd_1487231 : Nat := 4983230072969 + 3 ^ 40 * 1487231 * 2
def baseEnd_1487231 : Nat := 763664347266975935572855

theorem tailTrace_1487231 : CollatzResearch.WordTrace tailWord_1487231 prefixEnd_1487231 763664347266975935572855 := by
  unfold tailWord_1487231
  simp only [CollatzResearch.WordTrace]
  refine ⟨54243770875023560678029547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36162513916682373785353031 54243770875023560678029547)
  ·
    refine ⟨81365656312535341017044321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54243770875023560678029547 81365656312535341017044321)
    ·
      refine ⟨61024242234401505762783241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81365656312535341017044321 61024242234401505762783241)
      ·
        refine ⟨45768181675801129322087431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61024242234401505762783241 45768181675801129322087431)
        ·
          refine ⟨68652272513701693983131147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45768181675801129322087431 68652272513701693983131147)
          ·
            refine ⟨102978408770552540974696721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68652272513701693983131147 102978408770552540974696721)
            ·
              refine ⟨77233806577914405731022541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102978408770552540974696721 77233806577914405731022541)
              ·
                refine ⟨28962677466717902149133453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77233806577914405731022541 28962677466717902149133453)
                ·
                  refine ⟨10861004050019213305925045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28962677466717902149133453 10861004050019213305925045)
                  ·
                    refine ⟨1018219129689301247430473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10861004050019213305925045 1018219129689301247430473)
                    ·
                      refine ⟨763664347266975935572855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1018219129689301247430473 763664347266975935572855)
                      ·
                        rfl

theorem cell23_1487231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 5, 2].length) (baseStart_1487231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1487231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1487231 prefixEnd_1487231 := by exact prefixLift 1487231
  have htrace : WordTrace (prefixWord ++ tailWord_1487231) baseStart_1487231 baseEnd_1487231 := by
    simpa [prefixWord, tailWord_1487231, baseEnd_1487231] using wordTrace_append hprefix tailTrace_1487231
  have hstable : (prefixWord ++ tailWord_1487231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487231).length < 2 ^ (prefixWord ++ tailWord_1487231).sum := by decide
  have hdescent : baseEnd_1487231 < baseStart_1487231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487241 : List Nat := [1, 2, 1, 1, 6, 1, 2, 1, 3, 5]
def baseStart_1487241 : Nat := 118140960795 + 1487241 * 2 ^ 59
def prefixEnd_1487241 : Nat := 4983230072969 + 3 ^ 40 * 1487241 * 2
def baseEnd_1487241 : Nat := 254556494024506965482603

theorem tailTrace_1487241 : CollatzResearch.WordTrace tailWord_1487241 prefixEnd_1487241 254556494024506965482603 := by
  unfold tailWord_1487241
  simp only [CollatzResearch.WordTrace]
  refine ⟨54244135604987332385893577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36162757069991554923929051 54244135604987332385893577)
  ·
    refine ⟨40683101703740499289420183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54244135604987332385893577 40683101703740499289420183)
    ·
      refine ⟨61024652555610748934130275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40683101703740499289420183 61024652555610748934130275)
      ·
        refine ⟨91536978833416123401195413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61024652555610748934130275 91536978833416123401195413)
        ·
          refine ⟨4290795882816380784431035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 91536978833416123401195413 4290795882816380784431035)
          ·
            refine ⟨6436193824224571176646553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4290795882816380784431035 6436193824224571176646553)
            ·
              refine ⟨4827145368168428382484915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6436193824224571176646553 4827145368168428382484915)
              ·
                refine ⟨7240718052252642573727373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4827145368168428382484915 7240718052252642573727373)
                ·
                  refine ⟨2715269269594740965147765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7240718052252642573727373 2715269269594740965147765)
                  ·
                    refine ⟨254556494024506965482603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2715269269594740965147765 254556494024506965482603)
                    ·
                      rfl

theorem cell23_1487241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 3, 5].length) (baseStart_1487241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1487241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1487241 prefixEnd_1487241 := by exact prefixLift 1487241
  have htrace : WordTrace (prefixWord ++ tailWord_1487241) baseStart_1487241 baseEnd_1487241 := by
    simpa [prefixWord, tailWord_1487241, baseEnd_1487241] using wordTrace_append hprefix tailTrace_1487241
  have hstable : (prefixWord ++ tailWord_1487241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487241).length < 2 ^ (prefixWord ++ tailWord_1487241).sum := by decide
  have hdescent : baseEnd_1487241 < baseStart_1487241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487242 : List Nat := [3, 1, 2, 5, 1, 2, 1, 1, 2, 2, 3]
def baseStart_1487242 : Nat := 118140960795 + 1487242 * 2 ^ 59
def prefixEnd_1487242 : Nat := 4983230072969 + 3 ^ 40 * 1487242 * 2
def baseEnd_1487242 : Nat := 763669995554175392535305

theorem tailTrace_1487242 : CollatzResearch.WordTrace tailWord_1487242 prefixEnd_1487242 763669995554175392535305 := by
  unfold tailWord_1487242
  simp only [CollatzResearch.WordTrace]
  refine ⟨13561043019495927389169995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36162781385322473037786653 13561043019495927389169995)
  ·
    refine ⟨20341564529243891083754993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13561043019495927389169995 20341564529243891083754993)
    ·
      refine ⟨15256173396932918312816245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20341564529243891083754993 15256173396932918312816245)
      ·
        refine ⟨1430266255962461091826523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15256173396932918312816245 1430266255962461091826523)
        ·
          refine ⟨2145399383943691637739785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1430266255962461091826523 2145399383943691637739785)
          ·
            refine ⟨1609049537957768728304839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2145399383943691637739785 1609049537957768728304839)
            ·
              refine ⟨2413574306936653092457259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1609049537957768728304839 2413574306936653092457259)
              ·
                refine ⟨3620361460404979638685889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2413574306936653092457259 3620361460404979638685889)
                ·
                  refine ⟨2715271095303734729014417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3620361460404979638685889 2715271095303734729014417)
                  ·
                    refine ⟨2036453321477801046760813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2715271095303734729014417 2036453321477801046760813)
                    ·
                      refine ⟨763669995554175392535305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2036453321477801046760813 763669995554175392535305)
                      ·
                        rfl

theorem cell23_1487242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_1487242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1487242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1487242 prefixEnd_1487242 := by exact prefixLift 1487242
  have htrace : WordTrace (prefixWord ++ tailWord_1487242) baseStart_1487242 baseEnd_1487242 := by
    simpa [prefixWord, tailWord_1487242, baseEnd_1487242] using wordTrace_append hprefix tailTrace_1487242
  have hstable : (prefixWord ++ tailWord_1487242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487242).length < 2 ^ (prefixWord ++ tailWord_1487242).sum := by decide
  have hdescent : baseEnd_1487242 < baseStart_1487242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487255 : List Nat := [1, 1, 3, 3, 1, 1, 3, 5, 1, 1, 3]
def baseStart_1487255 : Nat := 118140960795 + 1487255 * 2 ^ 59
def prefixEnd_1487255 : Nat := 4983230072969 + 3 ^ 40 * 1487255 * 2
def baseEnd_1487255 : Nat := 763676670802683841672745

theorem tailTrace_1487255 : CollatzResearch.WordTrace tailWord_1487255 prefixEnd_1487255 763676670802683841672745 := by
  unfold tailWord_1487255
  simp only [CollatzResearch.WordTrace]
  refine ⟨54244646226936612776903219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36163097484624408517935479 54244646226936612776903219)
  ·
    refine ⟨81366969340404919165354829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54244646226936612776903219 81366969340404919165354829)
    ·
      refine ⟨30512613502651844687008061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81366969340404919165354829 30512613502651844687008061)
      ·
        refine ⟨11442230063494441757628023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30512613502651844687008061 11442230063494441757628023)
        ·
          refine ⟨17163345095241662636442035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11442230063494441757628023 17163345095241662636442035)
          ·
            refine ⟨25745017642862493954663053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17163345095241662636442035 25745017642862493954663053)
            ·
              refine ⟨9654381616073435232998645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25745017642862493954663053 9654381616073435232998645)
              ·
                refine ⟨905098276506884553093623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9654381616073435232998645 905098276506884553093623)
                ·
                  refine ⟨1357647414760326829640435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 905098276506884553093623 1357647414760326829640435)
                  ·
                    refine ⟨2036471122140490244460653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1357647414760326829640435 2036471122140490244460653)
                    ·
                      refine ⟨763676670802683841672745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2036471122140490244460653 763676670802683841672745)
                      ·
                        rfl

theorem cell23_1487255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 5, 1, 1, 3].length) (baseStart_1487255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1487255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1487255 prefixEnd_1487255 := by exact prefixLift 1487255
  have htrace : WordTrace (prefixWord ++ tailWord_1487255) baseStart_1487255 baseEnd_1487255 := by
    simpa [prefixWord, tailWord_1487255, baseEnd_1487255] using wordTrace_append hprefix tailTrace_1487255
  have hstable : (prefixWord ++ tailWord_1487255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487255).length < 2 ^ (prefixWord ++ tailWord_1487255).sum := by decide
  have hdescent : baseEnd_1487255 < baseStart_1487255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487258 : List Nat := [3, 1, 1, 4, 1, 3, 1, 3, 1, 5]
def baseStart_1487258 : Nat := 118140960795 + 1487258 * 2 ^ 59
def prefixEnd_1487258 : Nat := 4983230072969 + 3 ^ 40 * 1487258 * 2
def baseEnd_1487258 : Nat := 254559403748215776645077

theorem tailTrace_1487258 : CollatzResearch.WordTrace tailWord_1487258 prefixEnd_1487258 254559403748215776645077 := by
  unfold tailWord_1487258
  simp only [CollatzResearch.WordTrace]
  refine ⟨13561188911481436072315607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36163170430617162859508285 13561188911481436072315607)
  ·
    refine ⟨20341783367222154108473411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13561188911481436072315607 20341783367222154108473411)
    ·
      refine ⟨30512675050833231162710117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20341783367222154108473411 30512675050833231162710117)
      ·
        refine ⟨5721126572031230843008147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30512675050833231162710117 5721126572031230843008147)
        ·
          refine ⟨8581689858046846264512221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5721126572031230843008147 8581689858046846264512221)
          ·
            refine ⟨3218133696767567349192083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8581689858046846264512221 3218133696767567349192083)
            ·
              refine ⟨4827200545151351023788125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3218133696767567349192083 4827200545151351023788125)
              ·
                refine ⟨1810200204431756633920547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4827200545151351023788125 1810200204431756633920547)
                ·
                  refine ⟨2715300306647634950880821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1810200204431756633920547 2715300306647634950880821)
                  ·
                    refine ⟨254559403748215776645077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2715300306647634950880821 254559403748215776645077)
                    ·
                      rfl

theorem cell23_1487258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 3, 1, 5].length) (baseStart_1487258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1487258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1487258 prefixEnd_1487258 := by exact prefixLift 1487258
  have htrace : WordTrace (prefixWord ++ tailWord_1487258) baseStart_1487258 baseEnd_1487258 := by
    simpa [prefixWord, tailWord_1487258, baseEnd_1487258] using wordTrace_append hprefix tailTrace_1487258
  have hstable : (prefixWord ++ tailWord_1487258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487258).length < 2 ^ (prefixWord ++ tailWord_1487258).sum := by decide
  have hdescent : baseEnd_1487258 < baseStart_1487258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487272 : List Nat := [2, 1, 6, 1, 1, 2, 2, 1, 3, 1, 3]
def baseStart_1487272 : Nat := 118140960795 + 1487272 * 2 ^ 59
def prefixEnd_1487272 : Nat := 4983230072969 + 3 ^ 40 * 1487272 * 2
def baseEnd_1487272 : Nat := 763685399973810275160167

theorem tailTrace_1487272 : CollatzResearch.WordTrace tailWord_1487272 prefixEnd_1487272 763685399973810275160167 := by
  unfold tailWord_1487272
  simp only [CollatzResearch.WordTrace]
  refine ⟨27122633133937512340136035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36163510845250016453514713 27122633133937512340136035)
  ·
    refine ⟨40683949700906268510204053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27122633133937512340136035 40683949700906268510204053)
    ·
      refine ⟨1907060142229981336415815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 40683949700906268510204053 1907060142229981336415815)
      ·
        refine ⟨2860590213344972004623723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1907060142229981336415815 2860590213344972004623723)
        ·
          refine ⟨4290885320017458006935585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2860590213344972004623723 4290885320017458006935585)
          ·
            refine ⟨3218163990013093505201689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4290885320017458006935585 3218163990013093505201689)
            ·
              refine ⟨2413622992509820128901267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3218163990013093505201689 2413622992509820128901267)
              ·
                refine ⟨3620434488764730193351901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2413622992509820128901267 3620434488764730193351901)
                ·
                  refine ⟨1357662933286773822506963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3620434488764730193351901 1357662933286773822506963)
                  ·
                    refine ⟨2036494399930160733760445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1357662933286773822506963 2036494399930160733760445)
                    ·
                      refine ⟨763685399973810275160167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2036494399930160733760445 763685399973810275160167)
                      ·
                        rfl

theorem cell23_1487272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_1487272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1487272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1487272 prefixEnd_1487272 := by exact prefixLift 1487272
  have htrace : WordTrace (prefixWord ++ tailWord_1487272) baseStart_1487272 baseEnd_1487272 := by
    simpa [prefixWord, tailWord_1487272, baseEnd_1487272] using wordTrace_append hprefix tailTrace_1487272
  have hstable : (prefixWord ++ tailWord_1487272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487272).length < 2 ^ (prefixWord ++ tailWord_1487272).sum := by decide
  have hdescent : baseEnd_1487272 < baseStart_1487272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487281 : List Nat := [1, 2, 2, 4, 1, 2, 1, 1, 3, 1, 5]
def baseStart_1487281 : Nat := 118140960795 + 1487281 * 2 ^ 59
def prefixEnd_1487281 : Nat := 4983230072969 + 3 ^ 40 * 1487281 * 2
def baseEnd_1487281 : Nat := 763690021299700739947625

theorem tailTrace_1487281 : CollatzResearch.WordTrace tailWord_1487281 prefixEnd_1487281 763690021299700739947625 := by
  unfold tailWord_1487281
  simp only [CollatzResearch.WordTrace]
  refine ⟨54245594524842419217349697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36163729683228279478233131 54245594524842419217349697)
  ·
    refine ⟨40684195893631814413012273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54245594524842419217349697 40684195893631814413012273)
    ·
      refine ⟨30513146920223860809759205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40684195893631814413012273 30513146920223860809759205)
      ·
        refine ⟨5721215047541973901829851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30513146920223860809759205 5721215047541973901829851)
        ·
          refine ⟨8581822571312960852744777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5721215047541973901829851 8581822571312960852744777)
          ·
            refine ⟨6436366928484720639558583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8581822571312960852744777 6436366928484720639558583)
            ·
              refine ⟨9654550392727080959337875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6436366928484720639558583 9654550392727080959337875)
              ·
                refine ⟨14481825589090621439006813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9654550392727080959337875 14481825589090621439006813)
                ·
                  refine ⟨5430684595908983039627555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14481825589090621439006813 5430684595908983039627555)
                  ·
                    refine ⟨8146026893863474559441333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5430684595908983039627555 8146026893863474559441333)
                    ·
                      refine ⟨763690021299700739947625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8146026893863474559441333 763690021299700739947625)
                      ·
                        rfl

theorem cell23_1487281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_1487281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1487281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1487281 prefixEnd_1487281 := by exact prefixLift 1487281
  have htrace : WordTrace (prefixWord ++ tailWord_1487281) baseStart_1487281 baseEnd_1487281 := by
    simpa [prefixWord, tailWord_1487281, baseEnd_1487281] using wordTrace_append hprefix tailTrace_1487281
  have hstable : (prefixWord ++ tailWord_1487281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487281).length < 2 ^ (prefixWord ++ tailWord_1487281).sum := by decide
  have hdescent : baseEnd_1487281 < baseStart_1487281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487311 : List Nat := [1, 1, 2, 1, 1, 4, 1, 3, 3, 3, 3]
def baseStart_1487311 : Nat := 118140960795 + 1487311 * 2 ^ 59
def prefixEnd_1487311 : Nat := 4983230072969 + 3 ^ 40 * 1487311 * 2
def baseEnd_1487311 : Nat := 763705425719335622572487

theorem tailTrace_1487311 : CollatzResearch.WordTrace tailWord_1487311 prefixEnd_1487311 763705425719335622572487 := by
  unfold tailWord_1487311
  simp only [CollatzResearch.WordTrace]
  refine ⟨54246688714733734340941787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36164459143155822893961191 54246688714733734340941787)
  ·
    refine ⟨81370033072100601511412681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54246688714733734340941787 81370033072100601511412681)
    ·
      refine ⟨61027524804075451133559511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81370033072100601511412681 61027524804075451133559511)
      ·
        refine ⟨91541287206113176700339267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61027524804075451133559511 91541287206113176700339267)
        ·
          refine ⟨137311930809169765050508901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91541287206113176700339267 137311930809169765050508901)
          ·
            refine ⟨25745987026719330946970419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137311930809169765050508901 25745987026719330946970419)
            ·
              refine ⟨38618980540078996420455629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25745987026719330946970419 38618980540078996420455629)
              ·
                refine ⟨14482117702529623657670861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38618980540078996420455629 14482117702529623657670861)
                ·
                  refine ⟨5430794138448608871626573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14482117702529623657670861 5430794138448608871626573)
                  ·
                    refine ⟨2036547801918228326859965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5430794138448608871626573 2036547801918228326859965)
                    ·
                      refine ⟨763705425719335622572487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2036547801918228326859965 763705425719335622572487)
                      ·
                        rfl

theorem cell23_1487311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3, 3, 3].length) (baseStart_1487311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1487311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1487311 prefixEnd_1487311 := by exact prefixLift 1487311
  have htrace : WordTrace (prefixWord ++ tailWord_1487311) baseStart_1487311 baseEnd_1487311 := by
    simpa [prefixWord, tailWord_1487311, baseEnd_1487311] using wordTrace_append hprefix tailTrace_1487311
  have hstable : (prefixWord ++ tailWord_1487311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487311).length < 2 ^ (prefixWord ++ tailWord_1487311).sum := by decide
  have hdescent : baseEnd_1487311 < baseStart_1487311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487328 : List Nat := [2, 1, 1, 3, 1, 1, 3, 3, 4, 1, 3]
def baseStart_1487328 : Nat := 118140960795 + 1487328 * 2 ^ 59
def prefixEnd_1487328 : Nat := 4983230072969 + 3 ^ 40 * 1487328 * 2
def baseEnd_1487328 : Nat := 763714154890462056059909

theorem tailTrace_1487328 : CollatzResearch.WordTrace tailWord_1487328 prefixEnd_1487328 763714154890462056059909 := by
  unfold tailWord_1487328
  simp only [CollatzResearch.WordTrace]
  refine ⟨27123654377836073122155319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36164872503781430829540425 27123654377836073122155319)
  ·
    refine ⟨40685481566754109683232979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27123654377836073122155319 40685481566754109683232979)
    ·
      refine ⟨61028222350131164524849469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40685481566754109683232979 61028222350131164524849469)
      ·
        refine ⟨22885583381299186696818551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61028222350131164524849469 22885583381299186696818551)
        ·
          refine ⟨34328375071948780045227827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22885583381299186696818551 34328375071948780045227827)
          ·
            refine ⟨51492562607923170067841741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34328375071948780045227827 51492562607923170067841741)
            ·
              refine ⟨19309710977971188775440653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51492562607923170067841741 19309710977971188775440653)
              ·
                refine ⟨7241141616739195790790245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19309710977971188775440653 7241141616739195790790245)
                ·
                  refine ⟨1357714053138599210773171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7241141616739195790790245 1357714053138599210773171)
                  ·
                    refine ⟨2036571079707898816159757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1357714053138599210773171 2036571079707898816159757)
                    ·
                      refine ⟨763714154890462056059909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2036571079707898816159757 763714154890462056059909)
                      ·
                        rfl

theorem cell23_1487328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 4, 1, 3].length) (baseStart_1487328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1487328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1487328 prefixEnd_1487328 := by exact prefixLift 1487328
  have htrace : WordTrace (prefixWord ++ tailWord_1487328) baseStart_1487328 baseEnd_1487328 := by
    simpa [prefixWord, tailWord_1487328, baseEnd_1487328] using wordTrace_append hprefix tailTrace_1487328
  have hstable : (prefixWord ++ tailWord_1487328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487328).length < 2 ^ (prefixWord ++ tailWord_1487328).sum := by decide
  have hdescent : baseEnd_1487328 < baseStart_1487328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487329 : List Nat := [1, 2, 3, 1, 2, 2, 5, 2, 1, 2, 2]
def baseStart_1487329 : Nat := 118140960795 + 1487329 * 2 ^ 59
def prefixEnd_1487329 : Nat := 4983230072969 + 3 ^ 40 * 1487329 * 2
def baseEnd_1487329 : Nat := 763714668371116552147405

theorem tailTrace_1487329 : CollatzResearch.WordTrace tailWord_1487329 prefixEnd_1487329 763714668371116552147405 := by
  unfold tailWord_1487329
  simp only [CollatzResearch.WordTrace]
  refine ⟨54247345228668523415097041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36164896819112348943398027 54247345228668523415097041)
  ·
    refine ⟨40685508921501392561322781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54247345228668523415097041 40685508921501392561322781)
    ·
      refine ⟨15257065845563022210496043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40685508921501392561322781 15257065845563022210496043)
      ·
        refine ⟨22885598768344533315744065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15257065845563022210496043 22885598768344533315744065)
        ·
          refine ⟨17164199076258399986808049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22885598768344533315744065 17164199076258399986808049)
          ·
            refine ⟨12873149307193799990106037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17164199076258399986808049 12873149307193799990106037)
            ·
              refine ⟨1206857747549418749072441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12873149307193799990106037 1206857747549418749072441)
              ·
                refine ⟨905143310662064061804331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1206857747549418749072441 905143310662064061804331)
                ·
                  refine ⟨1357714965993096092706497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 905143310662064061804331 1357714965993096092706497)
                  ·
                    refine ⟨1018286224494822069529873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1357714965993096092706497 1018286224494822069529873)
                    ·
                      refine ⟨763714668371116552147405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1018286224494822069529873 763714668371116552147405)
                      ·
                        rfl

theorem cell23_1487329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 2, 1, 2, 2].length) (baseStart_1487329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1487329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1487329 prefixEnd_1487329 := by exact prefixLift 1487329
  have htrace : WordTrace (prefixWord ++ tailWord_1487329) baseStart_1487329 baseEnd_1487329 := by
    simpa [prefixWord, tailWord_1487329, baseEnd_1487329] using wordTrace_append hprefix tailTrace_1487329
  have hstable : (prefixWord ++ tailWord_1487329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487329).length < 2 ^ (prefixWord ++ tailWord_1487329).sum := by decide
  have hdescent : baseEnd_1487329 < baseStart_1487329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487345 : List Nat := [1, 2, 2, 2, 3, 1, 3, 3, 2, 1, 3]
def baseStart_1487345 : Nat := 118140960795 + 1487345 * 2 ^ 59
def prefixEnd_1487345 : Nat := 4983230072969 + 3 ^ 40 * 1487345 * 2
def baseEnd_1487345 : Nat := 763722884061588489547331

theorem tailTrace_1487345 : CollatzResearch.WordTrace tailWord_1487345 prefixEnd_1487345 763722884061588489547331 := by
  unfold tailWord_1487345
  simp only [CollatzResearch.WordTrace]
  refine ⟨54247928796610558147679489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36165285864407038765119659 54247928796610558147679489)
  ·
    refine ⟨40685946597457918610759617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54247928796610558147679489 40685946597457918610759617)
    ·
      refine ⟨30514459948093438958069713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40685946597457918610759617 30514459948093438958069713)
      ·
        refine ⟨22885844961070079218552285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30514459948093438958069713 22885844961070079218552285)
        ·
          refine ⟨8582191860401279706957107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22885844961070079218552285 8582191860401279706957107)
          ·
            refine ⟨12873287790601919560435661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8582191860401279706957107 12873287790601919560435661)
            ·
              refine ⟨4827482921475719835163373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12873287790601919560435661 4827482921475719835163373)
              ·
                refine ⟨1810306095553394938186265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4827482921475719835163373 1810306095553394938186265)
                ·
                  refine ⟨1357729571665046203639699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1810306095553394938186265 1357729571665046203639699)
                  ·
                    refine ⟨2036594357497569305459549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1357729571665046203639699 2036594357497569305459549)
                    ·
                      refine ⟨763722884061588489547331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2036594357497569305459549 763722884061588489547331)
                      ·
                        rfl

theorem cell23_1487345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 3, 2, 1, 3].length) (baseStart_1487345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1487345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1487345 prefixEnd_1487345 := by exact prefixLift 1487345
  have htrace : WordTrace (prefixWord ++ tailWord_1487345) baseStart_1487345 baseEnd_1487345 := by
    simpa [prefixWord, tailWord_1487345, baseEnd_1487345] using wordTrace_append hprefix tailTrace_1487345
  have hstable : (prefixWord ++ tailWord_1487345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487345).length < 2 ^ (prefixWord ++ tailWord_1487345).sum := by decide
  have hdescent : baseEnd_1487345 < baseStart_1487345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487349 : List Nat := [1, 3, 5, 1, 2, 2, 1, 2, 1, 2, 3]
def baseStart_1487349 : Nat := 118140960795 + 1487349 * 2 ^ 59
def prefixEnd_1487349 : Nat := 4983230072969 + 3 ^ 40 * 1487349 * 2
def baseEnd_1487349 : Nat := 763724937984206473897313

theorem tailTrace_1487349 : CollatzResearch.WordTrace tailWord_1487349 prefixEnd_1487349 763724937984206473897313 := by
  unfold tailWord_1487349
  simp only [CollatzResearch.WordTrace]
  refine ⟨54248074688596066830825101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36165383125730711220550067 54248074688596066830825101)
  ·
    refine ⟨20343028008223525061559413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54248074688596066830825101 20343028008223525061559413)
    ·
      refine ⟨1907158875770955474521195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20343028008223525061559413 1907158875770955474521195)
      ·
        refine ⟨2860738313656433211781793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1907158875770955474521195 2860738313656433211781793)
        ·
          refine ⟨2145553735242324908836345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2860738313656433211781793 2145553735242324908836345)
          ·
            refine ⟨1609165301431743681627259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2145553735242324908836345 1609165301431743681627259)
            ·
              refine ⟨2413747952147615522440889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1609165301431743681627259 2413747952147615522440889)
              ·
                refine ⟨1810310964110711641830667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2413747952147615522440889 1810310964110711641830667)
                ·
                  refine ⟨2715466446166067462746001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1810310964110711641830667 2715466446166067462746001)
                  ·
                    refine ⟨2036599834624550597059501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2715466446166067462746001 2036599834624550597059501)
                    ·
                      refine ⟨763724937984206473897313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2036599834624550597059501 763724937984206473897313)
                      ·
                        rfl

theorem cell23_1487349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_1487349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1487349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1487349 prefixEnd_1487349 := by exact prefixLift 1487349
  have htrace : WordTrace (prefixWord ++ tailWord_1487349) baseStart_1487349 baseEnd_1487349 := by
    simpa [prefixWord, tailWord_1487349, baseEnd_1487349] using wordTrace_append hprefix tailTrace_1487349
  have hstable : (prefixWord ++ tailWord_1487349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487349).length < 2 ^ (prefixWord ++ tailWord_1487349).sum := by decide
  have hdescent : baseEnd_1487349 < baseStart_1487349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487362 : List Nat := [3, 4, 1, 2, 2, 1, 1, 2, 1, 3, 3]
def baseStart_1487362 : Nat := 118140960795 + 1487362 * 2 ^ 59
def prefixEnd_1487362 : Nat := 4983230072969 + 3 ^ 40 * 1487362 * 2
def baseEnd_1487362 : Nat := 763731613232714923034753

theorem tailTrace_1487362 : CollatzResearch.WordTrace tailWord_1487362 prefixEnd_1487362 763731613232714923034753 := by
  unfold tailWord_1487362
  simp only [CollatzResearch.WordTrace]
  refine ⟨13562137209387242512762085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36165699225032646700698893 13562137209387242512762085)
  ·
    refine ⟨2542900726760107971142891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13562137209387242512762085 2542900726760107971142891)
    ·
      refine ⟨3814351090140161956714337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2542900726760107971142891 3814351090140161956714337)
      ·
        refine ⟨2860763317605121467535753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3814351090140161956714337 2860763317605121467535753)
        ·
          refine ⟨2145572488203841100651815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2860763317605121467535753 2145572488203841100651815)
          ·
            refine ⟨3218358732305761650977723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2145572488203841100651815 3218358732305761650977723)
            ·
              refine ⟨4827538098458642476466585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3218358732305761650977723 4827538098458642476466585)
              ·
                refine ⟨3620653573843981857349939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4827538098458642476466585 3620653573843981857349939)
                ·
                  refine ⟨5430980360765972786024909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3620653573843981857349939 5430980360765972786024909)
                  ·
                    refine ⟨2036617635287239794759341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5430980360765972786024909 2036617635287239794759341)
                    ·
                      refine ⟨763731613232714923034753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2036617635287239794759341 763731613232714923034753)
                      ·
                        rfl

theorem cell23_1487362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_1487362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1487362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1487362 prefixEnd_1487362 := by exact prefixLift 1487362
  have htrace : WordTrace (prefixWord ++ tailWord_1487362) baseStart_1487362 baseEnd_1487362 := by
    simpa [prefixWord, tailWord_1487362, baseEnd_1487362] using wordTrace_append hprefix tailTrace_1487362
  have hstable : (prefixWord ++ tailWord_1487362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487362).length < 2 ^ (prefixWord ++ tailWord_1487362).sum := by decide
  have hdescent : baseEnd_1487362 < baseStart_1487362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487388 : List Nat := [2, 2, 3, 1, 2, 2, 1, 1, 2, 4, 3]
def baseStart_1487388 : Nat := 118140960795 + 1487388 * 2 ^ 59
def prefixEnd_1487388 : Nat := 4983230072969 + 3 ^ 40 * 1487388 * 2
def baseEnd_1487388 : Nat := 763744963729731821309633

theorem tailTrace_1487388 : CollatzResearch.WordTrace tailWord_1487388 prefixEnd_1487388 763744963729731821309633 := by
  unfold tailWord_1487388
  simp only [CollatzResearch.WordTrace]
  refine ⟨27124748567727388245747409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36166331423636517660996545 27124748567727388245747409)
  ·
    refine ⟨20343561425795541184310557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27124748567727388245747409 20343561425795541184310557)
    ·
      refine ⟨7628835534673327944116459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20343561425795541184310557 7628835534673327944116459)
      ·
        refine ⟨11443253302009991916174689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7628835534673327944116459 11443253302009991916174689)
        ·
          refine ⟨8582439976507493937131017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11443253302009991916174689 8582439976507493937131017)
          ·
            refine ⟨6436829982380620452848263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8582439976507493937131017 6436829982380620452848263)
            ·
              refine ⟨9655244973570930679272395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6436829982380620452848263 9655244973570930679272395)
              ·
                refine ⟨14482867460356396018908593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9655244973570930679272395 14482867460356396018908593)
                ·
                  refine ⟨10862150595267297014181445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14482867460356396018908593 10862150595267297014181445)
                  ·
                    refine ⟨2036653236612618190159021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10862150595267297014181445 2036653236612618190159021)
                    ·
                      refine ⟨763744963729731821309633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2036653236612618190159021 763744963729731821309633)
                      ·
                        rfl

theorem cell23_1487388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_1487388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1487388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1487388 prefixEnd_1487388 := by exact prefixLift 1487388
  have htrace : WordTrace (prefixWord ++ tailWord_1487388) baseStart_1487388 baseEnd_1487388 := by
    simpa [prefixWord, tailWord_1487388, baseEnd_1487388] using wordTrace_append hprefix tailTrace_1487388
  have hstable : (prefixWord ++ tailWord_1487388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487388).length < 2 ^ (prefixWord ++ tailWord_1487388).sum := by decide
  have hdescent : baseEnd_1487388 < baseStart_1487388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487391 : List Nat := [1, 1, 2, 4, 1, 1, 1, 5, 7]
def baseStart_1487391 : Nat := 118140960795 + 1487391 * 2 ^ 59
def prefixEnd_1487391 : Nat := 4983230072969 + 3 ^ 40 * 1487391 * 2
def baseEnd_1487391 : Nat := 84860722685743923285791

theorem tailTrace_1487391 : CollatzResearch.WordTrace tailWord_1487391 prefixEnd_1487391 84860722685743923285791 := by
  unfold tailWord_1487391
  simp only [CollatzResearch.WordTrace]
  refine ⟨54249606554443908003854027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36166404369629272002569351 54249606554443908003854027)
  ·
    refine ⟨81374409831665862005781041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54249606554443908003854027 81374409831665862005781041)
    ·
      refine ⟨61030807373749396504335781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81374409831665862005781041 61030807373749396504335781)
      ·
        refine ⟨11443276382578011844562959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61030807373749396504335781 11443276382578011844562959)
        ·
          refine ⟨17164914573867017766844439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11443276382578011844562959 17164914573867017766844439)
          ·
            refine ⟨25747371860800526650266659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17164914573867017766844439 25747371860800526650266659)
            ·
              refine ⟨38621057791200789975399989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25747371860800526650266659 38621057791200789975399989)
              ·
                refine ⟨3620724167925074060193749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38621057791200789975399989 3620724167925074060193749)
                ·
                  refine ⟨84860722685743923285791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3620724167925074060193749 84860722685743923285791)
                  ·
                    rfl

theorem cell23_1487391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5, 7].length) (baseStart_1487391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1487391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1487391 prefixEnd_1487391 := by exact prefixLift 1487391
  have htrace : WordTrace (prefixWord ++ tailWord_1487391) baseStart_1487391 baseEnd_1487391 := by
    simpa [prefixWord, tailWord_1487391, baseEnd_1487391] using wordTrace_append hprefix tailTrace_1487391
  have hstable : (prefixWord ++ tailWord_1487391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487391).length < 2 ^ (prefixWord ++ tailWord_1487391).sum := by decide
  have hdescent : baseEnd_1487391 < baseStart_1487391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487402 : List Nat := [3, 1, 4, 1, 1, 3, 2, 1, 1, 4, 2]
def baseStart_1487402 : Nat := 118140960795 + 1487402 * 2 ^ 59
def prefixEnd_1487402 : Nat := 4983230072969 + 3 ^ 40 * 1487402 * 2
def baseEnd_1487402 : Nat := 763752152458894766534569

theorem tailTrace_1487402 : CollatzResearch.WordTrace tailWord_1487402 prefixEnd_1487402 763752152458894766534569 := by
  unfold tailWord_1487402
  simp only [CollatzResearch.WordTrace]
  refine ⟨13562501939351014220626115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36166671838269371255002973 13562501939351014220626115)
  ·
    refine ⟨20343752909026521330939173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13562501939351014220626115 20343752909026521330939173)
    ·
      refine ⟨3814453670442472749551095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20343752909026521330939173 3814453670442472749551095)
      ·
        refine ⟨5721680505663709124326643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3814453670442472749551095 5721680505663709124326643)
        ·
          refine ⟨8582520758495563686489965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5721680505663709124326643 8582520758495563686489965)
          ·
            refine ⟨3218445284435836382433737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8582520758495563686489965 3218445284435836382433737)
            ·
              refine ⟨2413833963326877286825303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3218445284435836382433737 2413833963326877286825303)
              ·
                refine ⟨3620750944990315930237955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2413833963326877286825303 3620750944990315930237955)
                ·
                  refine ⟨5431126417485473895356933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3620750944990315930237955 5431126417485473895356933)
                  ·
                    refine ⟨1018336203278526355379425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5431126417485473895356933 1018336203278526355379425)
                    ·
                      refine ⟨763752152458894766534569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1018336203278526355379425 763752152458894766534569)
                      ·
                        rfl

theorem cell23_1487402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_1487402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1487402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1487402 prefixEnd_1487402 := by exact prefixLift 1487402
  have htrace : WordTrace (prefixWord ++ tailWord_1487402) baseStart_1487402 baseEnd_1487402 := by
    simpa [prefixWord, tailWord_1487402, baseEnd_1487402] using wordTrace_append hprefix tailTrace_1487402
  have hstable : (prefixWord ++ tailWord_1487402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487402).length < 2 ^ (prefixWord ++ tailWord_1487402).sum := by decide
  have hdescent : baseEnd_1487402 < baseStart_1487402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487425 : List Nat := [1, 2, 5, 1, 1, 2, 1, 5, 5]
def baseStart_1487425 : Nat := 118140960795 + 1487425 * 2 ^ 59
def prefixEnd_1487425 : Nat := 4983230072969 + 3 ^ 40 * 1487425 * 2
def baseEnd_1487425 : Nat := 84862662501549797394107

theorem tailTrace_1487425 : CollatzResearch.WordTrace tailWord_1487425 prefixEnd_1487425 84862662501549797394107 := by
  unfold tailWord_1487425
  simp only [CollatzResearch.WordTrace]
  refine ⟨54250846636320731810591729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36167231090880487873727819 54250846636320731810591729)
  ·
    refine ⟨40688134977240548857943797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54250846636320731810591729 40688134977240548857943797)
    ·
      refine ⟨3814512654116301455432231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40688134977240548857943797 3814512654116301455432231)
      ·
        refine ⟨5721768981174452183148347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3814512654116301455432231 5721768981174452183148347)
        ·
          refine ⟨8582653471761678274722521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5721768981174452183148347 8582653471761678274722521)
          ·
            refine ⟨6436990103821258706041891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8582653471761678274722521 6436990103821258706041891)
            ·
              refine ⟨9655485155731888059062837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6436990103821258706041891 9655485155731888059062837)
              ·
                refine ⟨905201733349864505537141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9655485155731888059062837 905201733349864505537141)
                ·
                  refine ⟨84862662501549797394107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 905201733349864505537141 84862662501549797394107)
                  ·
                    rfl

theorem cell23_1487425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 5, 5].length) (baseStart_1487425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1487425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1487425 prefixEnd_1487425 := by exact prefixLift 1487425
  have htrace : WordTrace (prefixWord ++ tailWord_1487425) baseStart_1487425 baseEnd_1487425 := by
    simpa [prefixWord, tailWord_1487425, baseEnd_1487425] using wordTrace_append hprefix tailTrace_1487425
  have hstable : (prefixWord ++ tailWord_1487425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487425).length < 2 ^ (prefixWord ++ tailWord_1487425).sum := by decide
  have hdescent : baseEnd_1487425 < baseStart_1487425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487438 : List Nat := [4, 1, 1, 1, 1, 2, 2, 4, 2, 5]
def baseStart_1487438 : Nat := 118140960795 + 1487438 * 2 ^ 59
def prefixEnd_1487438 : Nat := 4983230072969 + 3 ^ 40 * 1487438 * 2
def baseEnd_1487438 : Nat := 254590212587485541894801

theorem tailTrace_1487438 : CollatzResearch.WordTrace tailWord_1487438 prefixEnd_1487438 254590212587485541894801 := by
  unfold tailWord_1487438
  simp only [CollatzResearch.WordTrace]
  refine ⟨6781415098159204378851871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36167547190182423353876645 6781415098159204378851871)
  ·
    refine ⟨10172122647238806568277807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6781415098159204378851871 10172122647238806568277807)
    ·
      refine ⟨15258183970858209852416711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10172122647238806568277807 15258183970858209852416711)
      ·
        refine ⟨22887275956287314778625067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15258183970858209852416711 22887275956287314778625067)
        ·
          refine ⟨34330913934430972167937601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22887275956287314778625067 34330913934430972167937601)
          ·
            refine ⟨25748185450823229125953201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34330913934430972167937601 25748185450823229125953201)
            ·
              refine ⟨19311139088117421844464901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25748185450823229125953201 19311139088117421844464901)
              ·
                refine ⟨3620838579022016595837169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19311139088117421844464901 3620838579022016595837169)
                ·
                  refine ⟨2715628934266512446877877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3620838579022016595837169 2715628934266512446877877)
                  ·
                    refine ⟨254590212587485541894801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2715628934266512446877877 254590212587485541894801)
                    ·
                      rfl

theorem cell23_1487438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4, 2, 5].length) (baseStart_1487438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1487438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1487438 prefixEnd_1487438 := by exact prefixLift 1487438
  have htrace : WordTrace (prefixWord ++ tailWord_1487438) baseStart_1487438 baseEnd_1487438 := by
    simpa [prefixWord, tailWord_1487438, baseEnd_1487438] using wordTrace_append hprefix tailTrace_1487438
  have hstable : (prefixWord ++ tailWord_1487438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487438).length < 2 ^ (prefixWord ++ tailWord_1487438).sum := by decide
  have hdescent : baseEnd_1487438 < baseStart_1487438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487495 : List Nat := [1, 1, 4, 2, 1, 2, 3, 2, 2, 2, 3]
def baseStart_1487495 : Nat := 118140960795 + 1487495 * 2 ^ 59
def prefixEnd_1487495 : Nat := 4983230072969 + 3 ^ 40 * 1487495 * 2
def baseEnd_1487495 : Nat := 763799906159762902671641

theorem tailTrace_1487495 : CollatzResearch.WordTrace tailWord_1487495 prefixEnd_1487495 763799906159762902671641 := by
  unfold tailWord_1487495
  simp only [CollatzResearch.WordTrace]
  refine ⟨54253399746067133765639939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36168933164044755843759959 54253399746067133765639939)
  ·
    refine ⟨81380099619100700648459909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54253399746067133765639939 81380099619100700648459909)
    ·
      refine ⟨15258768678581381371586233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81380099619100700648459909 15258768678581381371586233)
      ·
        refine ⟨11444076508936036028689675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15258768678581381371586233 11444076508936036028689675)
        ·
          refine ⟨17166114763404054043034513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11444076508936036028689675 17166114763404054043034513)
          ·
            refine ⟨12874586072553040532275885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17166114763404054043034513 12874586072553040532275885)
            ·
              refine ⟨4827969777207390199603457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12874586072553040532275885 4827969777207390199603457)
              ·
                refine ⟨3620977332905542649702593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4827969777207390199603457 3620977332905542649702593)
                ·
                  refine ⟨2715732999679156987276945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3620977332905542649702593 2715732999679156987276945)
                  ·
                    refine ⟨2036799749759367740457709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2715732999679156987276945 2036799749759367740457709)
                    ·
                      refine ⟨763799906159762902671641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2036799749759367740457709 763799906159762902671641)
                      ·
                        rfl

theorem cell23_1487495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_1487495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1487495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1487495 prefixEnd_1487495 := by exact prefixLift 1487495
  have htrace : WordTrace (prefixWord ++ tailWord_1487495) baseStart_1487495 baseEnd_1487495 := by
    simpa [prefixWord, tailWord_1487495, baseEnd_1487495] using wordTrace_append hprefix tailTrace_1487495
  have hstable : (prefixWord ++ tailWord_1487495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487495).length < 2 ^ (prefixWord ++ tailWord_1487495).sum := by decide
  have hdescent : baseEnd_1487495 < baseStart_1487495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487525 : List Nat := [1, 3, 1, 2, 1, 2, 1, 3, 5, 1, 3]
def baseStart_1487525 : Nat := 118140960795 + 1487525 * 2 ^ 59
def prefixEnd_1487525 : Nat := 4983230072969 + 3 ^ 40 * 1487525 * 2
def baseEnd_1487525 : Nat := 763815310579397785296503

theorem tailTrace_1487525 : CollatzResearch.WordTrace tailWord_1487525 prefixEnd_1487525 763815310579397785296503 := by
  unfold tailWord_1487525
  simp only [CollatzResearch.WordTrace]
  refine ⟨54254493935958448889232029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36169662623972299259488019 54254493935958448889232029)
  ·
    refine ⟨20345435225984418333462011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54254493935958448889232029 20345435225984418333462011)
    ·
      refine ⟨30518152838976627500193017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20345435225984418333462011 30518152838976627500193017)
      ·
        refine ⟨22888614629232470625144763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30518152838976627500193017 22888614629232470625144763)
        ·
          refine ⟨34332921943848705937717145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22888614629232470625144763 34332921943848705937717145)
          ·
            refine ⟨25749691457886529453287859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34332921943848705937717145 25749691457886529453287859)
            ·
              refine ⟨38624537186829794179931789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25749691457886529453287859 38624537186829794179931789)
              ·
                refine ⟨14484201445061172817474421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38624537186829794179931789 14484201445061172817474421)
                ·
                  refine ⟨1357893885474484951638227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14484201445061172817474421 1357893885474484951638227)
                  ·
                    refine ⟨2036840828211727427457341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1357893885474484951638227 2036840828211727427457341)
                    ·
                      refine ⟨763815310579397785296503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2036840828211727427457341 763815310579397785296503)
                      ·
                        rfl

theorem cell23_1487525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 5, 1, 3].length) (baseStart_1487525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1487525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1487525 prefixEnd_1487525 := by exact prefixLift 1487525
  have htrace : WordTrace (prefixWord ++ tailWord_1487525) baseStart_1487525 baseEnd_1487525 := by
    simpa [prefixWord, tailWord_1487525, baseEnd_1487525] using wordTrace_append hprefix tailTrace_1487525
  have hstable : (prefixWord ++ tailWord_1487525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487525).length < 2 ^ (prefixWord ++ tailWord_1487525).sum := by decide
  have hdescent : baseEnd_1487525 < baseStart_1487525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487552 : List Nat := [2, 1, 1, 2, 4, 2, 2, 2, 2, 3, 2]
def baseStart_1487552 : Nat := 118140960795 + 1487552 * 2 ^ 59
def prefixEnd_1487552 : Nat := 4983230072969 + 3 ^ 40 * 1487552 * 2
def baseEnd_1487552 : Nat := 763829174557069179658879

theorem tailTrace_1487552 : CollatzResearch.WordTrace tailWord_1487552 prefixEnd_1487552 763829174557069179658879 := by
  unfold tailWord_1487552
  simp only [CollatzResearch.WordTrace]
  refine ⟨27127739353430316250232455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36170319137907088333643273 27127739353430316250232455)
  ·
    refine ⟨40691609030145474375348683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27127739353430316250232455 40691609030145474375348683)
    ·
      refine ⟨61037413545218211563023025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40691609030145474375348683 61037413545218211563023025)
      ·
        refine ⟨45778060158913658672267269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61037413545218211563023025 45778060158913658672267269)
        ·
          refine ⟨8583386279796311001050113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45778060158913658672267269 8583386279796311001050113)
          ·
            refine ⟨6437539709847233250787585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8583386279796311001050113 6437539709847233250787585)
            ·
              refine ⟨4828154782385424938090689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6437539709847233250787585 4828154782385424938090689)
              ·
                refine ⟨3621116086789068703568017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4828154782385424938090689 3621116086789068703568017)
                ·
                  refine ⟨2715837065091801527676013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3621116086789068703568017 2715837065091801527676013)
                  ·
                    refine ⟨1018438899409425572878505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2715837065091801527676013 1018438899409425572878505)
                    ·
                      refine ⟨763829174557069179658879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1018438899409425572878505 763829174557069179658879)
                      ·
                        rfl

theorem cell23_1487552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2, 2, 3, 2].length) (baseStart_1487552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1487552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1487552 prefixEnd_1487552 := by exact prefixLift 1487552
  have htrace : WordTrace (prefixWord ++ tailWord_1487552) baseStart_1487552 baseEnd_1487552 := by
    simpa [prefixWord, tailWord_1487552, baseEnd_1487552] using wordTrace_append hprefix tailTrace_1487552
  have hstable : (prefixWord ++ tailWord_1487552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487552).length < 2 ^ (prefixWord ++ tailWord_1487552).sum := by decide
  have hdescent : baseEnd_1487552 < baseStart_1487552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487575 : List Nat := [1, 1, 3, 2, 1, 5, 2, 1, 1, 6]
def baseStart_1487575 : Nat := 118140960795 + 1487575 * 2 ^ 59
def prefixEnd_1487575 : Nat := 4983230072969 + 3 ^ 40 * 1487575 * 2
def baseEnd_1487575 : Nat := 254613661537374196557091

theorem tailTrace_1487575 : CollatzResearch.WordTrace tailWord_1487575 prefixEnd_1487575 254613661537374196557091 := by
  unfold tailWord_1487575
  simp only [CollatzResearch.WordTrace]
  refine ⟨54256317585777307428552179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36170878390518204952368119 54256317585777307428552179)
  ·
    refine ⟨81384476378665961142828269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54256317585777307428552179 81384476378665961142828269)
    ·
      refine ⟨30519178641999735428560601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81384476378665961142828269 30519178641999735428560601)
      ·
        refine ⟨22889383981499801571420451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30519178641999735428560601 22889383981499801571420451)
        ·
          refine ⟨34334075972249702357130677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22889383981499801571420451 34334075972249702357130677)
          ·
            refine ⟨3218819622398409595981001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34334075972249702357130677 3218819622398409595981001)
            ·
              refine ⟨2414114716798807196985751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3218819622398409595981001 2414114716798807196985751)
              ·
                refine ⟨3621172075198210795478627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2414114716798807196985751 3621172075198210795478627)
                ·
                  refine ⟨5431758112797316193217941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3621172075198210795478627 5431758112797316193217941)
                  ·
                    refine ⟨254613661537374196557091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5431758112797316193217941 254613661537374196557091)
                    ·
                      rfl

theorem cell23_1487575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 1, 1, 6].length) (baseStart_1487575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1487575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1487575 prefixEnd_1487575 := by exact prefixLift 1487575
  have htrace : WordTrace (prefixWord ++ tailWord_1487575) baseStart_1487575 baseEnd_1487575 := by
    simpa [prefixWord, tailWord_1487575, baseEnd_1487575] using wordTrace_append hprefix tailTrace_1487575
  have hstable : (prefixWord ++ tailWord_1487575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487575).length < 2 ^ (prefixWord ++ tailWord_1487575).sum := by decide
  have hdescent : baseEnd_1487575 < baseStart_1487575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487599 : List Nat := [1, 1, 2, 1, 5, 4, 2, 1, 1, 1, 4]
def baseStart_1487599 : Nat := 118140960795 + 1487599 * 2 ^ 59
def prefixEnd_1487599 : Nat := 4983230072969 + 3 ^ 40 * 1487599 * 2
def baseEnd_1487599 : Nat := 763853308147830495771163

theorem tailTrace_1487599 : CollatzResearch.WordTrace tailWord_1487599 prefixEnd_1487599 763853308147830495771163 := by
  unfold tailWord_1487599
  simp only [CollatzResearch.WordTrace]
  refine ⟨54257192937690359527425851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36171461958460239684950567 54257192937690359527425851)
  ·
    refine ⟨81385789406535539291138777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54257192937690359527425851 81385789406535539291138777)
    ·
      refine ⟨61039342054901654468354083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81385789406535539291138777 61039342054901654468354083)
      ·
        refine ⟨91559013082352481702531125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61039342054901654468354083 91559013082352481702531125)
        ·
          refine ⟨8583657476470545159612293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 91559013082352481702531125 8583657476470545159612293)
          ·
            refine ⟨1609435776838227217427305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8583657476470545159612293 1609435776838227217427305)
            ·
              refine ⟨1207076832628670413070479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1609435776838227217427305 1207076832628670413070479)
              ·
                refine ⟨1810615248943005619605719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1207076832628670413070479 1810615248943005619605719)
                ·
                  refine ⟨2715922873414508429408579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1810615248943005619605719 2715922873414508429408579)
                  ·
                    refine ⟨4073884310121762644112869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2715922873414508429408579 4073884310121762644112869)
                    ·
                      refine ⟨763853308147830495771163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4073884310121762644112869 763853308147830495771163)
                      ·
                        rfl

theorem cell23_1487599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 1, 1, 1, 4].length) (baseStart_1487599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1487599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1487599 prefixEnd_1487599 := by exact prefixLift 1487599
  have htrace : WordTrace (prefixWord ++ tailWord_1487599) baseStart_1487599 baseEnd_1487599 := by
    simpa [prefixWord, tailWord_1487599, baseEnd_1487599] using wordTrace_append hprefix tailTrace_1487599
  have hstable : (prefixWord ++ tailWord_1487599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487599).length < 2 ^ (prefixWord ++ tailWord_1487599).sum := by decide
  have hdescent : baseEnd_1487599 < baseStart_1487599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487639 : List Nat := [1, 1, 3, 4, 4, 1, 2, 7]
def baseStart_1487639 : Nat := 118140960795 + 1487639 * 2 ^ 59
def prefixEnd_1487639 : Nat := 4983230072969 + 3 ^ 40 * 1487639 * 2
def baseEnd_1487639 : Nat := 28291623976815197750777

theorem tailTrace_1487639 : CollatzResearch.WordTrace tailWord_1487639 prefixEnd_1487639 28291623976815197750777 := by
  unfold tailWord_1487639
  simp only [CollatzResearch.WordTrace]
  refine ⟨54258651857545446358881971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36172434571696964239254647 54258651857545446358881971)
  ·
    refine ⟨81387977786318169538322957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54258651857545446358881971 81387977786318169538322957)
    ·
      refine ⟨30520491669869313576871109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81387977786318169538322957 30520491669869313576871109)
      ·
        refine ⟨5722592188100496295663333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30520491669869313576871109 5722592188100496295663333)
        ·
          refine ⟨1072986035268843055436875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5722592188100496295663333 1072986035268843055436875)
          ·
            refine ⟨1609479052903264583155313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1072986035268843055436875 1609479052903264583155313)
            ·
              refine ⟨1207109289677448437366485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1609479052903264583155313 1207109289677448437366485)
              ·
                refine ⟨28291623976815197750777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1207109289677448437366485 28291623976815197750777)
                ·
                  rfl

theorem cell23_1487639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 7].length) (baseStart_1487639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1487639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1487639 prefixEnd_1487639 := by exact prefixLift 1487639
  have htrace : WordTrace (prefixWord ++ tailWord_1487639) baseStart_1487639 baseEnd_1487639 := by
    simpa [prefixWord, tailWord_1487639, baseEnd_1487639] using wordTrace_append hprefix tailTrace_1487639
  have hstable : (prefixWord ++ tailWord_1487639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487639).length < 2 ^ (prefixWord ++ tailWord_1487639).sum := by decide
  have hdescent : baseEnd_1487639 < baseStart_1487639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487712 : List Nat := [2, 1, 1, 3, 3, 1, 2, 5, 5]
def baseStart_1487712 : Nat := 118140960795 + 1487712 * 2 ^ 59
def prefixEnd_1487712 : Nat := 4983230072969 + 3 ^ 40 * 1487712 * 2
def baseEnd_1487712 : Nat := 84879036829087617073127

theorem tailTrace_1487712 : CollatzResearch.WordTrace tailWord_1487712 prefixEnd_1487712 84879036829087617073127 := by
  unfold tailWord_1487712
  simp only [CollatzResearch.WordTrace]
  refine ⟨27130657193140489913144695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36174209590853986550859593 27130657193140489913144695)
  ·
    refine ⟨40695985789710734869717043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27130657193140489913144695 40695985789710734869717043)
    ·
      refine ⟨61043978684566102304575565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40695985789710734869717043 61043978684566102304575565)
      ·
        refine ⟨22891492006712288364215837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61043978684566102304575565 22891492006712288364215837)
        ·
          refine ⟨8584309502517108136580939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22891492006712288364215837 8584309502517108136580939)
          ·
            refine ⟨12876464253775662204871409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8584309502517108136580939 12876464253775662204871409)
            ·
              refine ⟨9657348190331746653653557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12876464253775662204871409 9657348190331746653653557)
              ·
                refine ⟨905376392843601248780021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9657348190331746653653557 905376392843601248780021)
                ·
                  refine ⟨84879036829087617073127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 905376392843601248780021 84879036829087617073127)
                  ·
                    rfl

theorem cell23_1487712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 5, 5].length) (baseStart_1487712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1487712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1487712 prefixEnd_1487712 := by exact prefixLift 1487712
  have htrace : WordTrace (prefixWord ++ tailWord_1487712) baseStart_1487712 baseEnd_1487712 := by
    simpa [prefixWord, tailWord_1487712, baseEnd_1487712] using wordTrace_append hprefix tailTrace_1487712
  have hstable : (prefixWord ++ tailWord_1487712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487712).length < 2 ^ (prefixWord ++ tailWord_1487712).sum := by decide
  have hdescent : baseEnd_1487712 < baseStart_1487712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487725 : List Nat := [1, 5, 1, 1, 1, 1, 1, 2, 3, 7]
def baseStart_1487725 : Nat := 118140960795 + 1487725 * 2 ^ 59
def prefixEnd_1487725 : Nat := 4983230072969 + 3 ^ 40 * 1487725 * 2
def baseEnd_1487725 : Nat := 254639335570099000931861

theorem tailTrace_1487725 : CollatzResearch.WordTrace tailWord_1487725 prefixEnd_1487725 254639335570099000931861 := by
  unfold tailWord_1487725
  simp only [CollatzResearch.WordTrace]
  refine ⟨54261788535233883046512629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36174525690155922031008419 54261788535233883046512629)
  ·
    refine ⟨5087042675178176535610559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54261788535233883046512629 5087042675178176535610559)
    ·
      refine ⟨7630564012767264803415839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5087042675178176535610559 7630564012767264803415839)
      ·
        refine ⟨11445846019150897205123759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7630564012767264803415839 11445846019150897205123759)
        ·
          refine ⟨17168769028726345807685639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11445846019150897205123759 17168769028726345807685639)
          ·
            refine ⟨25753153543089518711528459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17168769028726345807685639 25753153543089518711528459)
            ·
              refine ⟨38629730314634278067292689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25753153543089518711528459 38629730314634278067292689)
              ·
                refine ⟨28972297735975708550469517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38629730314634278067292689 28972297735975708550469517)
                ·
                  refine ⟨10864611650990890706426069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28972297735975708550469517 10864611650990890706426069)
                  ·
                    refine ⟨254639335570099000931861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10864611650990890706426069 254639335570099000931861)
                    ·
                      rfl

theorem cell23_1487725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_1487725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1487725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1487725 prefixEnd_1487725 := by exact prefixLift 1487725
  have htrace : WordTrace (prefixWord ++ tailWord_1487725) baseStart_1487725 baseEnd_1487725 := by
    simpa [prefixWord, tailWord_1487725, baseEnd_1487725] using wordTrace_append hprefix tailTrace_1487725
  have hstable : (prefixWord ++ tailWord_1487725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487725).length < 2 ^ (prefixWord ++ tailWord_1487725).sum := by decide
  have hdescent : baseEnd_1487725 < baseStart_1487725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487729 : List Nat := [1, 2, 2, 2, 1, 4, 4, 2, 5]
def baseStart_1487729 : Nat := 118140960795 + 1487729 * 2 ^ 59
def prefixEnd_1487729 : Nat := 4983230072969 + 3 ^ 40 * 1487729 * 2
def baseEnd_1487729 : Nat := 84880006736990554127285

theorem tailTrace_1487729 : CollatzResearch.WordTrace tailWord_1487729 prefixEnd_1487729 84880006736990554127285 := by
  unfold tailWord_1487729
  simp only [CollatzResearch.WordTrace]
  refine ⟨54261934427219391729658241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36174622951479594486438827 54261934427219391729658241)
  ·
    refine ⟨40696450820414543797243681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54261934427219391729658241 40696450820414543797243681)
    ·
      refine ⟨30522338115310907847932761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40696450820414543797243681 30522338115310907847932761)
      ·
        refine ⟨22891753586483180885949571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30522338115310907847932761 22891753586483180885949571)
        ·
          refine ⟨34337630379724771328924357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22891753586483180885949571 34337630379724771328924357)
          ·
            refine ⟨6438305696198394624173317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34337630379724771328924357 6438305696198394624173317)
            ·
              refine ⟨1207182318037198992032497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6438305696198394624173317 1207182318037198992032497)
              ·
                refine ⟨905386738527899244024373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1207182318037198992032497 905386738527899244024373)
                ·
                  refine ⟨84880006736990554127285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 905386738527899244024373 84880006736990554127285)
                  ·
                    rfl

theorem cell23_1487729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 2, 5].length) (baseStart_1487729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1487729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1487729 prefixEnd_1487729 := by exact prefixLift 1487729
  have htrace : WordTrace (prefixWord ++ tailWord_1487729) baseStart_1487729 baseEnd_1487729 := by
    simpa [prefixWord, tailWord_1487729, baseEnd_1487729] using wordTrace_append hprefix tailTrace_1487729
  have hstable : (prefixWord ++ tailWord_1487729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487729).length < 2 ^ (prefixWord ++ tailWord_1487729).sum := by decide
  have hdescent : baseEnd_1487729 < baseStart_1487729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487746 : List Nat := [3, 4, 2, 2, 1, 1, 1, 2, 7]
def baseStart_1487746 : Nat := 118140960795 + 1487746 * 2 ^ 59
def prefixEnd_1487746 : Nat := 4983230072969 + 3 ^ 40 * 1487746 * 2
def baseEnd_1487746 : Nat := 84880976644893491181443

theorem tailTrace_1487746 : CollatzResearch.WordTrace tailWord_1487746 prefixEnd_1487746 84880976644893491181443 := by
  unfold tailWord_1487746
  simp only [CollatzResearch.WordTrace]
  refine ⟨13565638617039450908256773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36175036312105202422018061 13565638617039450908256773)
  ·
    refine ⟨2543557240694897045298145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13565638617039450908256773 2543557240694897045298145)
    ·
      refine ⟨1907667930521172783973609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2543557240694897045298145 1907667930521172783973609)
      ·
        refine ⟨1430750947890879587980207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1907667930521172783973609 1430750947890879587980207)
        ·
          refine ⟨2146126421836319381970311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1430750947890879587980207 2146126421836319381970311)
          ·
            refine ⟨3219189632754479072955467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2146126421836319381970311 3219189632754479072955467)
            ·
              refine ⟨4828784449131718609433201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3219189632754479072955467 4828784449131718609433201)
              ·
                refine ⟨3621588336848788957074901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4828784449131718609433201 3621588336848788957074901)
                ·
                  refine ⟨84880976644893491181443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3621588336848788957074901 84880976644893491181443)
                  ·
                    rfl

theorem cell23_1487746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_1487746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1487746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1487746 prefixEnd_1487746 := by exact prefixLift 1487746
  have htrace : WordTrace (prefixWord ++ tailWord_1487746) baseStart_1487746 baseEnd_1487746 := by
    simpa [prefixWord, tailWord_1487746, baseEnd_1487746] using wordTrace_append hprefix tailTrace_1487746
  have hstable : (prefixWord ++ tailWord_1487746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487746).length < 2 ^ (prefixWord ++ tailWord_1487746).sum := by decide
  have hdescent : baseEnd_1487746 < baseStart_1487746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487785 : List Nat := [1, 2, 1, 1, 1, 1, 7, 1, 8]
def baseStart_1487785 : Nat := 118140960795 + 1487785 * 2 ^ 59
def prefixEnd_1487785 : Nat := 4983230072969 + 3 ^ 40 * 1487785 * 2
def baseEnd_1487785 : Nat := 84883201727729640893923

theorem tailTrace_1487785 : CollatzResearch.WordTrace tailWord_1487785 prefixEnd_1487785 84883201727729640893923 := by
  unfold tailWord_1487785
  simp only [CollatzResearch.WordTrace]
  refine ⟨54263976915016513293696809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36175984610011008862464539 54263976915016513293696809)
  ·
    refine ⟨40697982686262384970272607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54263976915016513293696809 40697982686262384970272607)
    ·
      refine ⟨61046974029393577455408911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40697982686262384970272607 61046974029393577455408911)
      ·
        refine ⟨91570461044090366183113367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61046974029393577455408911 91570461044090366183113367)
        ·
          refine ⟨137355691566135549274670051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91570461044090366183113367 137355691566135549274670051)
          ·
            refine ⟨206033537349203323912005077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137355691566135549274670051 206033537349203323912005077)
            ·
              refine ⟨4828911031621952904187619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 206033537349203323912005077 4828911031621952904187619)
              ·
                refine ⟨7243366547432929356281429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4828911031621952904187619 7243366547432929356281429)
                ·
                  refine ⟨84883201727729640893923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7243366547432929356281429 84883201727729640893923)
                  ·
                    rfl

theorem cell23_1487785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 8].length) (baseStart_1487785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1487785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1487785 prefixEnd_1487785 := by exact prefixLift 1487785
  have htrace : WordTrace (prefixWord ++ tailWord_1487785) baseStart_1487785 baseEnd_1487785 := by
    simpa [prefixWord, tailWord_1487785, baseEnd_1487785] using wordTrace_append hprefix tailTrace_1487785
  have hstable : (prefixWord ++ tailWord_1487785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487785).length < 2 ^ (prefixWord ++ tailWord_1487785).sum := by decide
  have hdescent : baseEnd_1487785 < baseStart_1487785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487814 : List Nat := [6, 1, 3, 1, 2, 1, 1, 3, 5]
def baseStart_1487814 : Nat := 118140960795 + 1487814 * 2 ^ 59
def prefixEnd_1487814 : Nat := 4983230072969 + 3 ^ 40 * 1487814 * 2
def baseEnd_1487814 : Nat := 84884856276505239398075

theorem tailTrace_1487814 : CollatzResearch.WordTrace tailWord_1487814 prefixEnd_1487814 84884856276505239398075 := by
  unfold tailWord_1487814
  simp only [CollatzResearch.WordTrace]
  refine ⟨1695782332247232851453203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 36176689754607634164334997 1695782332247232851453203)
  ·
    refine ⟨2543673498370849277179805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1695782332247232851453203 2543673498370849277179805)
    ·
      refine ⟨953877561889068478942427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2543673498370849277179805 953877561889068478942427)
      ·
        refine ⟨1430816342833602718413641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 953877561889068478942427 1430816342833602718413641)
        ·
          refine ⟨1073112257125202038810231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1430816342833602718413641 1073112257125202038810231)
          ·
            refine ⟨1609668385687803058215347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1073112257125202038810231 1609668385687803058215347)
            ·
              refine ⟨2414502578531704587323021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1609668385687803058215347 2414502578531704587323021)
              ·
                refine ⟨905438466949389220246133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2414502578531704587323021 905438466949389220246133)
                ·
                  refine ⟨84884856276505239398075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 905438466949389220246133 84884856276505239398075)
                  ·
                    rfl

theorem cell23_1487814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_1487814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1487814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1487814 prefixEnd_1487814 := by exact prefixLift 1487814
  have htrace : WordTrace (prefixWord ++ tailWord_1487814) baseStart_1487814 baseEnd_1487814 := by
    simpa [prefixWord, tailWord_1487814, baseEnd_1487814] using wordTrace_append hprefix tailTrace_1487814
  have hstable : (prefixWord ++ tailWord_1487814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487814).length < 2 ^ (prefixWord ++ tailWord_1487814).sum := by decide
  have hdescent : baseEnd_1487814 < baseStart_1487814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487889 : List Nat := [1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 3]
def baseStart_1487889 : Nat := 118140960795 + 1487889 * 2 ^ 59
def prefixEnd_1487889 : Nat := 4983230072969 + 3 ^ 40 * 1487889 * 2
def baseEnd_1487889 : Nat := 764002217537634361144829

theorem tailTrace_1487889 : CollatzResearch.WordTrace tailWord_1487889 prefixEnd_1487889 764002217537634361144829 := by
  unfold tailWord_1487889
  simp only [CollatzResearch.WordTrace]
  refine ⟨54267770106639739055482721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36178513404426492703655147 54267770106639739055482721)
  ·
    refine ⟨40700827579979804291612041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54267770106639739055482721 40700827579979804291612041)
    ·
      refine ⟨30525620684984853218709031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40700827579979804291612041 30525620684984853218709031)
      ·
        refine ⟨45788431027477279828063547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30525620684984853218709031 45788431027477279828063547)
        ·
          refine ⟨68682646541215919742095321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45788431027477279828063547 68682646541215919742095321)
          ·
            refine ⟨51511984905911939806571491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68682646541215919742095321 51511984905911939806571491)
            ·
              refine ⟨77267977358867909709857237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51511984905911939806571491 77267977358867909709857237)
              ·
                refine ⟨1810968219348466633824779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 77267977358867909709857237 1810968219348466633824779)
                ·
                  refine ⟨2716452329022699950737169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1810968219348466633824779 2716452329022699950737169)
                  ·
                    refine ⟨2037339246767024963052877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2716452329022699950737169 2037339246767024963052877)
                    ·
                      refine ⟨764002217537634361144829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2037339246767024963052877 764002217537634361144829)
                      ·
                        rfl

theorem cell23_1487889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 3].length) (baseStart_1487889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1487889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1487889 prefixEnd_1487889 := by exact prefixLift 1487889
  have htrace : WordTrace (prefixWord ++ tailWord_1487889) baseStart_1487889 baseEnd_1487889 := by
    simpa [prefixWord, tailWord_1487889, baseEnd_1487889] using wordTrace_append hprefix tailTrace_1487889
  have hstable : (prefixWord ++ tailWord_1487889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487889).length < 2 ^ (prefixWord ++ tailWord_1487889).sum := by decide
  have hdescent : baseEnd_1487889 < baseStart_1487889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487892 : List Nat := [2, 4, 3, 14]
def baseStart_1487892 : Nat := 118140960795 + 1487892 * 2 ^ 59
def prefixEnd_1487892 : Nat := 4983230072969 + 3 ^ 40 * 1487892 * 2
def baseEnd_1487892 : Nat := 349338709638590694745

theorem tailTrace_1487892 : CollatzResearch.WordTrace tailWord_1487892 prefixEnd_1487892 349338709638590694745 := by
  unfold tailWord_1487892
  simp only [CollatzResearch.WordTrace]
  refine ⟨27133939762814435283920965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36178586350419247045227953 27133939762814435283920965)
  ·
    refine ⟨5087613705527706615735181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27133939762814435283920965 5087613705527706615735181)
    ·
      refine ⟨1907855139572889980900693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5087613705527706615735181 1907855139572889980900693)
      ·
        refine ⟨349338709638590694745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 1907855139572889980900693 349338709638590694745)
        ·
          rfl

theorem cell23_1487892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 14].length) (baseStart_1487892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1487892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1487892 prefixEnd_1487892 := by exact prefixLift 1487892
  have htrace : WordTrace (prefixWord ++ tailWord_1487892) baseStart_1487892 baseEnd_1487892 := by
    simpa [prefixWord, tailWord_1487892, baseEnd_1487892] using wordTrace_append hprefix tailTrace_1487892
  have hstable : (prefixWord ++ tailWord_1487892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487892).length < 2 ^ (prefixWord ++ tailWord_1487892).sum := by decide
  have hdescent : baseEnd_1487892 < baseStart_1487892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487896 : List Nat := [2, 1, 2, 3, 2, 3, 2, 2, 2, 4]
def baseStart_1487896 : Nat := 118140960795 + 1487896 * 2 ^ 59
def prefixEnd_1487896 : Nat := 4983230072969 + 3 ^ 40 * 1487896 * 2
def baseEnd_1487896 : Nat := 254668603967405277919099

theorem tailTrace_1487896 : CollatzResearch.WordTrace tailWord_1487896 prefixEnd_1487896 254668603967405277919099 := by
  unfold tailWord_1487896
  simp only [CollatzResearch.WordTrace]
  refine ⟨27134012708807189625493771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36178683611742919500658361 27134012708807189625493771)
  ·
    refine ⟨40701019063210784438240657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27134012708807189625493771 40701019063210784438240657)
    ·
      refine ⟨30525764297408088328680493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40701019063210784438240657 30525764297408088328680493)
      ·
        refine ⟨11447161611528033123255185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30525764297408088328680493 11447161611528033123255185)
        ·
          refine ⟨8585371208646024842441389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11447161611528033123255185 8585371208646024842441389)
          ·
            refine ⟨3219514203242259315915521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8585371208646024842441389 3219514203242259315915521)
            ·
              refine ⟨2414635652431694486936641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3219514203242259315915521 2414635652431694486936641)
              ·
                refine ⟨1810976739323770865202481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2414635652431694486936641 1810976739323770865202481)
                ·
                  refine ⟨1358232554492828148901861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1810976739323770865202481 1358232554492828148901861)
                  ·
                    refine ⟨254668603967405277919099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1358232554492828148901861 254668603967405277919099)
                    ·
                      rfl

theorem cell23_1487896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 2, 2, 4].length) (baseStart_1487896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1487896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1487896 prefixEnd_1487896 := by exact prefixLift 1487896
  have htrace : WordTrace (prefixWord ++ tailWord_1487896) baseStart_1487896 baseEnd_1487896 := by
    simpa [prefixWord, tailWord_1487896, baseEnd_1487896] using wordTrace_append hprefix tailTrace_1487896
  have hstable : (prefixWord ++ tailWord_1487896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487896).length < 2 ^ (prefixWord ++ tailWord_1487896).sum := by decide
  have hdescent : baseEnd_1487896 < baseStart_1487896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487922 : List Nat := [3, 2, 1, 1, 2, 2, 1, 2, 2, 7]
def baseStart_1487922 : Nat := 118140960795 + 1487922 * 2 ^ 59
def prefixEnd_1487922 : Nat := 4983230072969 + 3 ^ 40 * 1487922 * 2
def baseEnd_1487922 : Nat := 254673054133077577344059

theorem tailTrace_1487922 : CollatzResearch.WordTrace tailWord_1487922 prefixEnd_1487922 254673054133077577344059 := by
  unfold tailWord_1487922
  simp only [CollatzResearch.WordTrace]
  refine ⟨13567243428880046422858505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36179315810346790460956013 13567243428880046422858505)
  ·
    refine ⟨10175432571660034817143879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13567243428880046422858505 10175432571660034817143879)
    ·
      refine ⟨15263148857490052225715819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10175432571660034817143879 15263148857490052225715819)
      ·
        refine ⟨22894723286235078338573729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15263148857490052225715819 22894723286235078338573729)
        ·
          refine ⟨17171042464676308753930297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22894723286235078338573729 17171042464676308753930297)
          ·
            refine ⟨12878281848507231565447723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17171042464676308753930297 12878281848507231565447723)
            ·
              refine ⟨19317422772760847348171585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12878281848507231565447723 19317422772760847348171585)
              ·
                refine ⟨14488067079570635511128689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19317422772760847348171585 14488067079570635511128689)
                ·
                  refine ⟨10866050309677976633346517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14488067079570635511128689 10866050309677976633346517)
                  ·
                    refine ⟨254673054133077577344059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10866050309677976633346517 254673054133077577344059)
                    ·
                      rfl

theorem cell23_1487922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 2, 7].length) (baseStart_1487922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1487922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1487922 prefixEnd_1487922 := by exact prefixLift 1487922
  have htrace : WordTrace (prefixWord ++ tailWord_1487922) baseStart_1487922 baseEnd_1487922 := by
    simpa [prefixWord, tailWord_1487922, baseEnd_1487922] using wordTrace_append hprefix tailTrace_1487922
  have hstable : (prefixWord ++ tailWord_1487922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487922).length < 2 ^ (prefixWord ++ tailWord_1487922).sum := by decide
  have hdescent : baseEnd_1487922 < baseStart_1487922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487926 : List Nat := [5, 1, 2, 1, 1, 3, 3, 7]
def baseStart_1487926 : Nat := 118140960795 + 1487926 * 2 ^ 59
def prefixEnd_1487926 : Nat := 4983230072969 + 3 ^ 40 * 1487926 * 2
def baseEnd_1487926 : Nat := 28297082085994470977117

theorem tailTrace_1487926 : CollatzResearch.WordTrace tailWord_1487926 prefixEnd_1487926 28297082085994470977117 := by
  unfold tailWord_1487926
  simp only [CollatzResearch.WordTrace]
  refine ⟨3391819975469105898411227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36179413071670462916386421 3391819975469105898411227)
  ·
    refine ⟨5087729963203658847616841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3391819975469105898411227 5087729963203658847616841)
    ·
      refine ⟨3815797472402744135712631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5087729963203658847616841 3815797472402744135712631)
      ·
        refine ⟨5723696208604116203568947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3815797472402744135712631 5723696208604116203568947)
        ·
          refine ⟨8585544312906174305353421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5723696208604116203568947 8585544312906174305353421)
          ·
            refine ⟨3219579117339815364507533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8585544312906174305353421 3219579117339815364507533)
            ·
              refine ⟨1207342169002430761690325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3219579117339815364507533 1207342169002430761690325)
              ·
                refine ⟨28297082085994470977117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1207342169002430761690325 28297082085994470977117)
                ·
                  rfl

theorem cell23_1487926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 7].length) (baseStart_1487926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1487926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1487926 prefixEnd_1487926 := by exact prefixLift 1487926
  have htrace : WordTrace (prefixWord ++ tailWord_1487926) baseStart_1487926 baseEnd_1487926 := by
    simpa [prefixWord, tailWord_1487926, baseEnd_1487926] using wordTrace_append hprefix tailTrace_1487926
  have hstable : (prefixWord ++ tailWord_1487926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487926).length < 2 ^ (prefixWord ++ tailWord_1487926).sum := by decide
  have hdescent : baseEnd_1487926 < baseStart_1487926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487937 : List Nat := [1, 2, 5, 1, 3, 1, 2, 3, 1, 2, 2]
def baseStart_1487937 : Nat := 118140960795 + 1487937 * 2 ^ 59
def prefixEnd_1487937 : Nat := 4983230072969 + 3 ^ 40 * 1487937 * 2
def baseEnd_1487937 : Nat := 764026864609050173344609

theorem tailTrace_1487937 : CollatzResearch.WordTrace tailWord_1487937 prefixEnd_1487937 764026864609050173344609 := by
  unfold tailWord_1487937
  simp only [CollatzResearch.WordTrace]
  refine ⟨54269520810465843253230065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36179680540310562168820043 54269520810465843253230065)
  ·
    refine ⟨40702140607849382439922549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54269520810465843253230065 40702140607849382439922549)
    ·
      refine ⟨3815825681985879603742739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40702140607849382439922549 3815825681985879603742739)
      ·
        refine ⟨5723738522978819405614109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3815825681985879603742739 5723738522978819405614109)
        ·
          refine ⟨2146401946117057277105291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5723738522978819405614109 2146401946117057277105291)
          ·
            refine ⟨3219602919175585915657937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2146401946117057277105291 3219602919175585915657937)
            ·
              refine ⟨2414702189381689436743453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3219602919175585915657937 2414702189381689436743453)
              ·
                refine ⟨905513321018133538778795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2414702189381689436743453 905513321018133538778795)
                ·
                  refine ⟨1358269981527200308168193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 905513321018133538778795 1358269981527200308168193)
                  ·
                    refine ⟨1018702486145400231126145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1358269981527200308168193 1018702486145400231126145)
                    ·
                      refine ⟨764026864609050173344609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1018702486145400231126145 764026864609050173344609)
                      ·
                        rfl

theorem cell23_1487937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_1487937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1487937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1487937 prefixEnd_1487937 := by exact prefixLift 1487937
  have htrace : WordTrace (prefixWord ++ tailWord_1487937) baseStart_1487937 baseEnd_1487937 := by
    simpa [prefixWord, tailWord_1487937, baseEnd_1487937] using wordTrace_append hprefix tailTrace_1487937
  have hstable : (prefixWord ++ tailWord_1487937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487937).length < 2 ^ (prefixWord ++ tailWord_1487937).sum := by decide
  have hdescent : baseEnd_1487937 < baseStart_1487937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487962 : List Nat := [3, 1, 1, 2, 1, 1, 2, 1, 3, 3, 5]
def baseStart_1487962 : Nat := 118140960795 + 1487962 * 2 ^ 59
def prefixEnd_1487962 : Nat := 4983230072969 + 3 ^ 40 * 1487962 * 2
def baseEnd_1487962 : Nat := 764039701625412575531993

theorem tailTrace_1487962 : CollatzResearch.WordTrace tailWord_1487962 prefixEnd_1487962 764039701625412575531993 := by
  unfold tailWord_1487962
  simp only [CollatzResearch.WordTrace]
  refine ⟨13567608158843818130722535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36180288423583515015260093 13567608158843818130722535)
  ·
    refine ⟨20351412238265727196083803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13567608158843818130722535 20351412238265727196083803)
    ·
      refine ⟨30527118357398590794125705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20351412238265727196083803 30527118357398590794125705)
      ·
        refine ⟨22895338768048943095594279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30527118357398590794125705 22895338768048943095594279)
        ·
          refine ⟨34343008152073414643391419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22895338768048943095594279 34343008152073414643391419)
          ·
            refine ⟨51514512228110121965087129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34343008152073414643391419 51514512228110121965087129)
            ·
              refine ⟨38635884171082591473815347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51514512228110121965087129 38635884171082591473815347)
              ·
                refine ⟨57953826256623887210723021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38635884171082591473815347 57953826256623887210723021)
                ·
                  refine ⟨21732684846233957704021133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57953826256623887210723021 21732684846233957704021133)
                  ·
                    refine ⟨8149756817337734139007925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21732684846233957704021133 8149756817337734139007925)
                    ·
                      refine ⟨764039701625412575531993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8149756817337734139007925 764039701625412575531993)
                      ·
                        rfl

theorem cell23_1487962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_1487962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1487962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1487962 prefixEnd_1487962 := by exact prefixLift 1487962
  have htrace : WordTrace (prefixWord ++ tailWord_1487962) baseStart_1487962 baseEnd_1487962 := by
    simpa [prefixWord, tailWord_1487962, baseEnd_1487962] using wordTrace_append hprefix tailTrace_1487962
  have hstable : (prefixWord ++ tailWord_1487962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487962).length < 2 ^ (prefixWord ++ tailWord_1487962).sum := by decide
  have hdescent : baseEnd_1487962 < baseStart_1487962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488029 : List Nat := [1, 4, 2, 1, 1, 2, 1, 2, 4, 5]
def baseStart_1488029 : Nat := 118140960795 + 1488029 * 2 ^ 59
def prefixEnd_1488029 : Nat := 4983230072969 + 3 ^ 40 * 1488029 * 2
def baseEnd_1488029 : Nat := 254691368276421271131395

theorem tailTrace_1488029 : CollatzResearch.WordTrace tailWord_1488029 prefixEnd_1488029 254691368276421271131395 := by
  unfold tailWord_1488029
  simp only [CollatzResearch.WordTrace]
  refine ⟨54272876326132542965579141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36181917550755028643719427 54272876326132542965579141)
  ·
    refine ⟨10176164311149851806046089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54272876326132542965579141 10176164311149851806046089)
    ·
      refine ⟨7632123233362388854534567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10176164311149851806046089 7632123233362388854534567)
      ·
        refine ⟨11448184850043583281801851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7632123233362388854534567 11448184850043583281801851)
        ·
          refine ⟨17172277275065374922702777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11448184850043583281801851 17172277275065374922702777)
          ·
            refine ⟨12879207956299031192027083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17172277275065374922702777 12879207956299031192027083)
            ·
              refine ⟨19318811934448546788040625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12879207956299031192027083 19318811934448546788040625)
              ·
                refine ⟨14489108950836410091030469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19318811934448546788040625 14489108950836410091030469)
                ·
                  refine ⟨2716707928281826892068213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14489108950836410091030469 2716707928281826892068213)
                  ·
                    refine ⟨254691368276421271131395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2716707928281826892068213 254691368276421271131395)
                    ·
                      rfl

theorem cell23_1488029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_1488029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1488029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1488029 prefixEnd_1488029 := by exact prefixLift 1488029
  have htrace : WordTrace (prefixWord ++ tailWord_1488029) baseStart_1488029 baseEnd_1488029 := by
    simpa [prefixWord, tailWord_1488029, baseEnd_1488029] using wordTrace_append hprefix tailTrace_1488029
  have hstable : (prefixWord ++ tailWord_1488029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488029).length < 2 ^ (prefixWord ++ tailWord_1488029).sum := by decide
  have hdescent : baseEnd_1488029 < baseStart_1488029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488059 : List Nat := [1, 1, 1, 1, 1, 2, 4, 1, 7, 4]
def baseStart_1488059 : Nat := 118140960795 + 1488059 * 2 ^ 59
def prefixEnd_1488059 : Nat := 4983230072969 + 3 ^ 40 * 1488059 * 2
def baseEnd_1488059 : Nat := 254696503082966232006349

theorem tailTrace_1488059 : CollatzResearch.WordTrace tailWord_1488059 prefixEnd_1488059 254696503082966232006349 := by
  unfold tailWord_1488059
  simp only [CollatzResearch.WordTrace]
  refine ⟨54273970516023858089171231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36182647010682572059447487 54273970516023858089171231)
  ·
    refine ⟨81410955774035787133756847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54273970516023858089171231 81410955774035787133756847)
    ·
      refine ⟨122116433661053680700635271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81410955774035787133756847 122116433661053680700635271)
      ·
        refine ⟨183174650491580521050952907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122116433661053680700635271 183174650491580521050952907)
        ·
          refine ⟨274761975737370781576429361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183174650491580521050952907 274761975737370781576429361)
          ·
            refine ⟨206071481803028086182322021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 274761975737370781576429361 206071481803028086182322021)
            ·
              refine ⟨38638402838067766159185379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 206071481803028086182322021 38638402838067766159185379)
              ·
                refine ⟨57957604257101649238778069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38638402838067766159185379 57957604257101649238778069)
                ·
                  refine ⟨1358381349775819904033861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 57957604257101649238778069 1358381349775819904033861)
                  ·
                    refine ⟨254696503082966232006349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1358381349775819904033861 254696503082966232006349)
                    ·
                      rfl

theorem cell23_1488059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 7, 4].length) (baseStart_1488059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1488059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1488059 prefixEnd_1488059 := by exact prefixLift 1488059
  have htrace : WordTrace (prefixWord ++ tailWord_1488059) baseStart_1488059 baseEnd_1488059 := by
    simpa [prefixWord, tailWord_1488059, baseEnd_1488059] using wordTrace_append hprefix tailTrace_1488059
  have hstable : (prefixWord ++ tailWord_1488059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488059).length < 2 ^ (prefixWord ++ tailWord_1488059).sum := by decide
  have hdescent : baseEnd_1488059 < baseStart_1488059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488069 : List Nat := [1, 3, 1, 1, 1, 1, 3, 2, 3, 4, 3]
def baseStart_1488069 : Nat := 118140960795 + 1488069 * 2 ^ 59
def prefixEnd_1488069 : Nat := 4983230072969 + 3 ^ 40 * 1488069 * 2
def baseEnd_1488069 : Nat := 764094644055443656894001

theorem tailTrace_1488069 : CollatzResearch.WordTrace tailWord_1488069 prefixEnd_1488069 764094644055443656894001 := by
  unfold tailWord_1488069
  simp only [CollatzResearch.WordTrace]
  refine ⟨54274335245987629797035261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36182890163991753198023507 54274335245987629797035261)
  ·
    refine ⟨20352875717245361173888223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54274335245987629797035261 20352875717245361173888223)
    ·
      refine ⟨30529313575868041760832335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20352875717245361173888223 30529313575868041760832335)
      ·
        refine ⟨45793970363802062641248503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30529313575868041760832335 45793970363802062641248503)
        ·
          refine ⟨68690955545703093961872755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45793970363802062641248503 68690955545703093961872755)
          ·
            refine ⟨103036433318554640942809133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68690955545703093961872755 103036433318554640942809133)
            ·
              refine ⟨38638662494457990353553425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103036433318554640942809133 38638662494457990353553425)
              ·
                refine ⟨28978996870843492765165069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38638662494457990353553425 28978996870843492765165069)
                ·
                  refine ⟨10867123826566309786936901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28978996870843492765165069 10867123826566309786936901)
                  ·
                    refine ⟨2037585717481183085050669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10867123826566309786936901 2037585717481183085050669)
                    ·
                      refine ⟨764094644055443656894001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2037585717481183085050669 764094644055443656894001)
                      ·
                        rfl

theorem cell23_1488069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 4, 3].length) (baseStart_1488069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1488069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1488069 prefixEnd_1488069 := by exact prefixLift 1488069
  have htrace : WordTrace (prefixWord ++ tailWord_1488069) baseStart_1488069 baseEnd_1488069 := by
    simpa [prefixWord, tailWord_1488069, baseEnd_1488069] using wordTrace_append hprefix tailTrace_1488069
  have hstable : (prefixWord ++ tailWord_1488069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488069).length < 2 ^ (prefixWord ++ tailWord_1488069).sum := by decide
  have hdescent : baseEnd_1488069 < baseStart_1488069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488103 : List Nat := [1, 1, 5, 3, 2, 1, 1, 1, 1, 4, 3]
def baseStart_1488103 : Nat := 118140960795 + 1488103 * 2 ^ 59
def prefixEnd_1488103 : Nat := 4983230072969 + 3 ^ 40 * 1488103 * 2
def baseEnd_1488103 : Nat := 764112102397696523868845

theorem tailTrace_1488103 : CollatzResearch.WordTrace tailWord_1488103 prefixEnd_1488103 764112102397696523868845 := by
  unfold tailWord_1488103
  simp only [CollatzResearch.WordTrace]
  refine ⟨54275575327864453603772963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36183716885242969069181975 54275575327864453603772963)
  ·
    refine ⟨81413362991796680405659445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54275575327864453603772963 81413362991796680405659445)
    ·
      refine ⟨7632502780480938788030573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81413362991796680405659445 7632502780480938788030573)
      ·
        refine ⟨2862188542680352045511465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7632502780480938788030573 2862188542680352045511465)
        ·
          refine ⟨2146641407010264034133599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2862188542680352045511465 2146641407010264034133599)
          ·
            refine ⟨3219962110515396051200399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2146641407010264034133599 3219962110515396051200399)
            ·
              refine ⟨4829943165773094076800599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3219962110515396051200399 4829943165773094076800599)
              ·
                refine ⟨7244914748659641115200899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4829943165773094076800599 7244914748659641115200899)
                ·
                  refine ⟨10867372122989461672801349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7244914748659641115200899 10867372122989461672801349)
                  ·
                    refine ⟨2037632273060524063650253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10867372122989461672801349 2037632273060524063650253)
                    ·
                      refine ⟨764112102397696523868845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2037632273060524063650253 764112102397696523868845)
                      ·
                        rfl

theorem cell23_1488103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_1488103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1488103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1488103 prefixEnd_1488103 := by exact prefixLift 1488103
  have htrace : WordTrace (prefixWord ++ tailWord_1488103) baseStart_1488103 baseEnd_1488103 := by
    simpa [prefixWord, tailWord_1488103, baseEnd_1488103] using wordTrace_append hprefix tailTrace_1488103
  have hstable : (prefixWord ++ tailWord_1488103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488103).length < 2 ^ (prefixWord ++ tailWord_1488103).sum := by decide
  have hdescent : baseEnd_1488103 < baseStart_1488103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488126 : List Nat := [4, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6]
def baseStart_1488126 : Nat := 118140960795 + 1488126 * 2 ^ 59
def prefixEnd_1488126 : Nat := 4983230072969 + 3 ^ 40 * 1488126 * 2
def baseEnd_1488126 : Nat := 764123912452749933881239

theorem tailTrace_1488126 : CollatzResearch.WordTrace tailWord_1488126 prefixEnd_1488126 764123912452749933881239 := by
  unfold tailWord_1488126
  simp only [CollatzResearch.WordTrace]
  refine ⟨6784551775847641066482529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36184276137854085687906821 6784551775847641066482529)
  ·
    refine ⟨5088413831885730799861897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6784551775847641066482529 5088413831885730799861897)
    ·
      refine ⟨3816310373914298099896423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5088413831885730799861897 3816310373914298099896423)
      ·
        refine ⟨5724465560871447149844635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3816310373914298099896423 5724465560871447149844635)
        ·
          refine ⟨8586698341307170724766953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5724465560871447149844635 8586698341307170724766953)
          ·
            refine ⟨6440023755980378043575215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8586698341307170724766953 6440023755980378043575215)
            ·
              refine ⟨9660035633970567065362823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6440023755980378043575215 9660035633970567065362823)
              ·
                refine ⟨14490053450955850598044235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9660035633970567065362823 14490053450955850598044235)
                ·
                  refine ⟨21735080176433775897066353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14490053450955850598044235 21735080176433775897066353)
                  ·
                    refine ⟨16301310132325331922799765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21735080176433775897066353 16301310132325331922799765)
                    ·
                      refine ⟨764123912452749933881239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16301310132325331922799765 764123912452749933881239)
                      ·
                        rfl

theorem cell23_1488126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_1488126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1488126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1488126 prefixEnd_1488126 := by exact prefixLift 1488126
  have htrace : WordTrace (prefixWord ++ tailWord_1488126) baseStart_1488126 baseEnd_1488126 := by
    simpa [prefixWord, tailWord_1488126, baseEnd_1488126] using wordTrace_append hprefix tailTrace_1488126
  have hstable : (prefixWord ++ tailWord_1488126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488126).length < 2 ^ (prefixWord ++ tailWord_1488126).sum := by decide
  have hdescent : baseEnd_1488126 < baseStart_1488126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488133 : List Nat := [1, 3, 1, 1, 2, 1, 6, 1, 3, 1, 3]
def baseStart_1488133 : Nat := 118140960795 + 1488133 * 2 ^ 59
def prefixEnd_1488133 : Nat := 4983230072969 + 3 ^ 40 * 1488133 * 2
def baseEnd_1488133 : Nat := 764127506817331406493707

theorem tailTrace_1488133 : CollatzResearch.WordTrace tailWord_1488133 prefixEnd_1488133 764127506817331406493707 := by
  unfold tailWord_1488133
  simp only [CollatzResearch.WordTrace]
  refine ⟨54276669517755768727365053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36184446345170512484910035 54276669517755768727365053)
  ·
    refine ⟨20353751069158413272761895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54276669517755768727365053 20353751069158413272761895)
    ·
      refine ⟨30530626603737619909142843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20353751069158413272761895 30530626603737619909142843)
      ·
        refine ⟨45795939905606429863714265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30530626603737619909142843 45795939905606429863714265)
        ·
          refine ⟨34346954929204822397785699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45795939905606429863714265 34346954929204822397785699)
          ·
            refine ⟨51520432393807233596678549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34346954929204822397785699 51520432393807233596678549)
            ·
              refine ⟨2415020268459714074844307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 51520432393807233596678549 2415020268459714074844307)
              ·
                refine ⟨3622530402689571112266461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2415020268459714074844307 3622530402689571112266461)
                ·
                  refine ⟨1358448901008589167099923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3622530402689571112266461 1358448901008589167099923)
                  ·
                    refine ⟨2037673351512883750649885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1358448901008589167099923 2037673351512883750649885)
                    ·
                      refine ⟨764127506817331406493707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2037673351512883750649885 764127506817331406493707)
                      ·
                        rfl

theorem cell23_1488133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 1, 3, 1, 3].length) (baseStart_1488133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1488133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1488133 prefixEnd_1488133 := by exact prefixLift 1488133
  have htrace : WordTrace (prefixWord ++ tailWord_1488133) baseStart_1488133 baseEnd_1488133 := by
    simpa [prefixWord, tailWord_1488133, baseEnd_1488133] using wordTrace_append hprefix tailTrace_1488133
  have hstable : (prefixWord ++ tailWord_1488133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488133).length < 2 ^ (prefixWord ++ tailWord_1488133).sum := by decide
  have hdescent : baseEnd_1488133 < baseStart_1488133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488156 : List Nat := [2, 2, 3, 1, 1, 1, 2, 3, 3, 1, 4]
def baseStart_1488156 : Nat := 118140960795 + 1488156 * 2 ^ 59
def prefixEnd_1488156 : Nat := 4983230072969 + 3 ^ 40 * 1488156 * 2
def baseEnd_1488156 : Nat := 764139316872384816506101

theorem tailTrace_1488156 : CollatzResearch.WordTrace tailWord_1488156 prefixEnd_1488156 764139316872384816506101 := by
  unfold tailWord_1488156
  simp only [CollatzResearch.WordTrace]
  refine ⟨27138754198336221827726161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36185005597781629103634881 27138754198336221827726161)
  ·
    refine ⟨20354065648752166370794621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27138754198336221827726161 20354065648752166370794621)
    ·
      refine ⟨7632774618282062389047983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20354065648752166370794621 7632774618282062389047983)
      ·
        refine ⟨11449161927423093583571975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7632774618282062389047983 11449161927423093583571975)
        ·
          refine ⟨17173742891134640375357963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11449161927423093583571975 17173742891134640375357963)
          ·
            refine ⟨25760614336701960563036945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17173742891134640375357963 25760614336701960563036945)
            ·
              refine ⟨19320460752526470422277709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25760614336701960563036945 19320460752526470422277709)
              ·
                refine ⟨7245172782197426408354141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19320460752526470422277709 7245172782197426408354141)
                ·
                  refine ⟨2716939793324034903132803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7245172782197426408354141 2716939793324034903132803)
                  ·
                    refine ⟨4075409689986052354699205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2716939793324034903132803 4075409689986052354699205)
                    ·
                      refine ⟨764139316872384816506101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4075409689986052354699205 764139316872384816506101)
                      ·
                        rfl

theorem cell23_1488156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_1488156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1488156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1488156 prefixEnd_1488156 := by exact prefixLift 1488156
  have htrace : WordTrace (prefixWord ++ tailWord_1488156) baseStart_1488156 baseEnd_1488156 := by
    simpa [prefixWord, tailWord_1488156, baseEnd_1488156] using wordTrace_append hprefix tailTrace_1488156
  have hstable : (prefixWord ++ tailWord_1488156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488156).length < 2 ^ (prefixWord ++ tailWord_1488156).sum := by decide
  have hdescent : baseEnd_1488156 < baseStart_1488156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488176 : List Nat := [2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 5]
def baseStart_1488176 : Nat := 118140960795 + 1488176 * 2 ^ 59
def prefixEnd_1488176 : Nat := 4983230072969 + 3 ^ 40 * 1488176 * 2
def baseEnd_1488176 : Nat := 764149586485474738256009

theorem tailTrace_1488176 : CollatzResearch.WordTrace tailWord_1488176 prefixEnd_1488176 764149586485474738256009 := by
  unfold tailWord_1488176
  simp only [CollatzResearch.WordTrace]
  refine ⟨27139118928299993535590191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36185491904399991380786921 27139118928299993535590191)
  ·
    refine ⟨40708678392449990303385287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27139118928299993535590191 40708678392449990303385287)
    ·
      refine ⟨61063017588674985455077931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40708678392449990303385287 61063017588674985455077931)
      ·
        refine ⟨91594526383012478182616897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61063017588674985455077931 91594526383012478182616897)
        ·
          refine ⟨68695894787259358636962673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91594526383012478182616897 68695894787259358636962673)
          ·
            refine ⟨51521921090444518977722005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68695894787259358636962673 51521921090444518977722005)
            ·
              refine ⟨2415090051114586827080719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 51521921090444518977722005 2415090051114586827080719)
              ·
                refine ⟨3622635076671880240621079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2415090051114586827080719 3622635076671880240621079)
                ·
                  refine ⟨5433952615007820360931619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3622635076671880240621079 5433952615007820360931619)
                  ·
                    refine ⟨8150928922511730541397429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5433952615007820360931619 8150928922511730541397429)
                    ·
                      refine ⟨764149586485474738256009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8150928922511730541397429 764149586485474738256009)
                      ·
                        rfl

theorem cell23_1488176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 5].length) (baseStart_1488176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1488176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1488176 prefixEnd_1488176 := by exact prefixLift 1488176
  have htrace : WordTrace (prefixWord ++ tailWord_1488176) baseStart_1488176 baseEnd_1488176 := by
    simpa [prefixWord, tailWord_1488176, baseEnd_1488176] using wordTrace_append hprefix tailTrace_1488176
  have hstable : (prefixWord ++ tailWord_1488176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488176).length < 2 ^ (prefixWord ++ tailWord_1488176).sum := by decide
  have hdescent : baseEnd_1488176 < baseStart_1488176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488179 : List Nat := [1, 1, 1, 2, 5, 2, 11]
def baseStart_1488179 : Nat := 118140960795 + 1488179 * 2 ^ 59
def prefixEnd_1488179 : Nat := 4983230072969 + 3 ^ 40 * 1488179 * 2
def baseEnd_1488179 : Nat := 9433964529968373166895

theorem tailTrace_1488179 : CollatzResearch.WordTrace tailWord_1488179 prefixEnd_1488179 9433964529968373166895 := by
  unfold tailWord_1488179
  simp only [CollatzResearch.WordTrace]
  refine ⟨54278347275589118583539591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36185564850392745722359727 54278347275589118583539591)
  ·
    refine ⟨81417520913383677875309387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54278347275589118583539591 81417520913383677875309387)
    ·
      refine ⟨122126281370075516812964081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81417520913383677875309387 122126281370075516812964081)
      ·
        refine ⟨91594711027556637609723061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122126281370075516812964081 91594711027556637609723061)
        ·
          refine ⟨8587004158833434775911537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 91594711027556637609723061 8587004158833434775911537)
          ·
            refine ⟨6440253119125076081933653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8587004158833434775911537 6440253119125076081933653)
            ·
              refine ⟨9433964529968373166895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 6440253119125076081933653 9433964529968373166895)
              ·
                rfl

theorem cell23_1488179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 11].length) (baseStart_1488179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1488179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1488179 prefixEnd_1488179 := by exact prefixLift 1488179
  have htrace : WordTrace (prefixWord ++ tailWord_1488179) baseStart_1488179 baseEnd_1488179 := by
    simpa [prefixWord, tailWord_1488179, baseEnd_1488179] using wordTrace_append hprefix tailTrace_1488179
  have hstable : (prefixWord ++ tailWord_1488179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488179).length < 2 ^ (prefixWord ++ tailWord_1488179).sum := by decide
  have hdescent : baseEnd_1488179 < baseStart_1488179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488193 : List Nat := [1, 2, 5, 2, 1, 1, 2, 2, 1, 1, 5]
def baseStart_1488193 : Nat := 118140960795 + 1488193 * 2 ^ 59
def prefixEnd_1488193 : Nat := 4983230072969 + 3 ^ 40 * 1488193 * 2
def baseEnd_1488193 : Nat := 764158315656601171743431

theorem tailTrace_1488193 : CollatzResearch.WordTrace tailWord_1488193 prefixEnd_1488193 764158315656601171743431 := by
  unfold tailWord_1488193
  simp only [CollatzResearch.WordTrace]
  refine ⟨54278857897538398974549233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36185905265025599316366155 54278857897538398974549233)
  ·
    refine ⟨40709143423153799230911925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54278857897538398974549233 40709143423153799230911925)
    ·
      refine ⟨3816482195920668677897993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40709143423153799230911925 3816482195920668677897993)
      ·
        refine ⟨2862361646940501508423495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3816482195920668677897993 2862361646940501508423495)
        ·
          refine ⟨4293542470410752262635243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2862361646940501508423495 4293542470410752262635243)
          ·
            refine ⟨6440313705616128393952865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4293542470410752262635243 6440313705616128393952865)
            ·
              refine ⟨4830235279212096295464649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6440313705616128393952865 4830235279212096295464649)
              ·
                refine ⟨3622676459409072221598487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4830235279212096295464649 3622676459409072221598487)
                ·
                  refine ⟨5434014689113608332397731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3622676459409072221598487 5434014689113608332397731)
                  ·
                    refine ⟨8151022033670412498596597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5434014689113608332397731 8151022033670412498596597)
                    ·
                      refine ⟨764158315656601171743431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8151022033670412498596597 764158315656601171743431)
                      ·
                        rfl

theorem cell23_1488193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_1488193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1488193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1488193 prefixEnd_1488193 := by exact prefixLift 1488193
  have htrace : WordTrace (prefixWord ++ tailWord_1488193) baseStart_1488193 baseEnd_1488193 := by
    simpa [prefixWord, tailWord_1488193, baseEnd_1488193] using wordTrace_append hprefix tailTrace_1488193
  have hstable : (prefixWord ++ tailWord_1488193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488193).length < 2 ^ (prefixWord ++ tailWord_1488193).sum := by decide
  have hdescent : baseEnd_1488193 < baseStart_1488193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488240 : List Nat := [2, 1, 1, 1, 4, 2, 4, 2, 2, 1, 3]
def baseStart_1488240 : Nat := 118140960795 + 1488240 * 2 ^ 59
def prefixEnd_1488240 : Nat := 4983230072969 + 3 ^ 40 * 1488240 * 2
def baseEnd_1488240 : Nat := 764182449247362487855715

theorem tailTrace_1488240 : CollatzResearch.WordTrace tailWord_1488240 prefixEnd_1488240 764182449247362487855715 := by
  unfold tailWord_1488240
  simp only [CollatzResearch.WordTrace]
  refine ⟨27140286064184063000755087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36187048085578750667673449 27140286064184063000755087)
  ·
    refine ⟨40710429096276094501132631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27140286064184063000755087 40710429096276094501132631)
    ·
      refine ⟨61065643644414141751698947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40710429096276094501132631 61065643644414141751698947)
      ·
        refine ⟨91598465466621212627548421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61065643644414141751698947 91598465466621212627548421)
        ·
          refine ⟨17174712274991477367665329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91598465466621212627548421 17174712274991477367665329)
          ·
            refine ⟨12881034206243608025748997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17174712274991477367665329 12881034206243608025748997)
            ·
              refine ⟨2415193913670676504827937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12881034206243608025748997 2415193913670676504827937)
              ·
                refine ⟨1811395435253007378620953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2415193913670676504827937 1811395435253007378620953)
                ·
                  refine ⟨1358546576439755533965715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1811395435253007378620953 1358546576439755533965715)
                  ·
                    refine ⟨2037819864659633300948573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1358546576439755533965715 2037819864659633300948573)
                    ·
                      refine ⟨764182449247362487855715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2037819864659633300948573 764182449247362487855715)
                      ·
                        rfl

theorem cell23_1488240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 2, 2, 1, 3].length) (baseStart_1488240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1488240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1488240 prefixEnd_1488240 := by exact prefixLift 1488240
  have htrace : WordTrace (prefixWord ++ tailWord_1488240) baseStart_1488240 baseEnd_1488240 := by
    simpa [prefixWord, tailWord_1488240, baseEnd_1488240] using wordTrace_append hprefix tailTrace_1488240
  have hstable : (prefixWord ++ tailWord_1488240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488240).length < 2 ^ (prefixWord ++ tailWord_1488240).sum := by decide
  have hdescent : baseEnd_1488240 < baseStart_1488240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488284 : List Nat := [2, 2, 3, 4, 1, 1, 1, 3, 1, 3, 2]
def baseStart_1488284 : Nat := 118140960795 + 1488284 * 2 ^ 59
def prefixEnd_1488284 : Nat := 4983230072969 + 3 ^ 40 * 1488284 * 2
def baseEnd_1488284 : Nat := 764205042396160315705513

theorem tailTrace_1488284 : CollatzResearch.WordTrace tailWord_1488284 prefixEnd_1488284 764205042396160315705513 := by
  unfold tailWord_1488284
  simp only [CollatzResearch.WordTrace]
  refine ⟨27141088470104360758055953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36188117960139147677407937 27141088470104360758055953)
  ·
    refine ⟨20355816352578270568541965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27141088470104360758055953 20355816352578270568541965)
    ·
      refine ⟨7633431132216851463203237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20355816352578270568541965 7633431132216851463203237)
      ·
        refine ⟨1431268337290659649350607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7633431132216851463203237 1431268337290659649350607)
        ·
          refine ⟨2146902505935989474025911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1431268337290659649350607 2146902505935989474025911)
          ·
            refine ⟨3220353758903984211038867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2146902505935989474025911 3220353758903984211038867)
            ·
              refine ⟨4830530638355976316558301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3220353758903984211038867 4830530638355976316558301)
              ·
                refine ⟨1811448989383491118709363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4830530638355976316558301 1811448989383491118709363)
                ·
                  refine ⟨2717173484075236678064045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1811448989383491118709363 2717173484075236678064045)
                  ·
                    refine ⟨1018940056528213754274017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2717173484075236678064045 1018940056528213754274017)
                    ·
                      refine ⟨764205042396160315705513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1018940056528213754274017 764205042396160315705513)
                      ·
                        rfl

theorem cell23_1488284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_1488284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1488284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1488284 prefixEnd_1488284 := by exact prefixLift 1488284
  have htrace : WordTrace (prefixWord ++ tailWord_1488284) baseStart_1488284 baseEnd_1488284 := by
    simpa [prefixWord, tailWord_1488284, baseEnd_1488284] using wordTrace_append hprefix tailTrace_1488284
  have hstable : (prefixWord ++ tailWord_1488284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488284).length < 2 ^ (prefixWord ++ tailWord_1488284).sum := by decide
  have hdescent : baseEnd_1488284 < baseStart_1488284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488323 : List Nat := [1, 1, 1, 3, 1, 1, 4, 2, 2, 5, 2]
def baseStart_1488323 : Nat := 118140960795 + 1488323 * 2 ^ 59
def prefixEnd_1488323 : Nat := 4983230072969 + 3 ^ 40 * 1488323 * 2
def baseEnd_1488323 : Nat := 764225068141685663117833

theorem tailTrace_1488323 : CollatzResearch.WordTrace tailWord_1488323 prefixEnd_1488323 764225068141685663117833 := by
  unfold tailWord_1488323
  simp only [CollatzResearch.WordTrace]
  refine ⟨54283599387067431176781623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36189066258044954117854415 54283599387067431176781623)
  ·
    refine ⟨81425399080601146765172435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54283599387067431176781623 81425399080601146765172435)
    ·
      refine ⟨122138098620901720147758653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81425399080601146765172435 122138098620901720147758653)
      ·
        refine ⟨45801786982838145055409495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122138098620901720147758653 45801786982838145055409495)
        ·
          refine ⟨68702680474257217583114243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45801786982838145055409495 68702680474257217583114243)
          ·
            refine ⟨103054020711385826374671365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68702680474257217583114243 103054020711385826374671365)
            ·
              refine ⟨19322628883384842445250881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103054020711385826374671365 19322628883384842445250881)
              ·
                refine ⟨14491971662538631833938161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19322628883384842445250881 14491971662538631833938161)
                ·
                  refine ⟨10868978746903973875453621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14491971662538631833938161 10868978746903973875453621)
                  ·
                    refine ⟨1018966757522247550823777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10868978746903973875453621 1018966757522247550823777)
                    ·
                      refine ⟨764225068141685663117833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1018966757522247550823777 764225068141685663117833)
                      ·
                        rfl

theorem cell23_1488323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 5, 2].length) (baseStart_1488323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1488323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1488323 prefixEnd_1488323 := by exact prefixLift 1488323
  have htrace : WordTrace (prefixWord ++ tailWord_1488323) baseStart_1488323 baseEnd_1488323 := by
    simpa [prefixWord, tailWord_1488323, baseEnd_1488323] using wordTrace_append hprefix tailTrace_1488323
  have hstable : (prefixWord ++ tailWord_1488323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488323).length < 2 ^ (prefixWord ++ tailWord_1488323).sum := by decide
  have hdescent : baseEnd_1488323 < baseStart_1488323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488353 : List Nat := [1, 2, 3, 1, 2, 3, 1, 1, 4, 1, 4]
def baseStart_1488353 : Nat := 118140960795 + 1488353 * 2 ^ 59
def prefixEnd_1488353 : Nat := 4983230072969 + 3 ^ 40 * 1488353 * 2
def baseEnd_1488353 : Nat := 764240472561320545742695

theorem tailTrace_1488353 : CollatzResearch.WordTrace tailWord_1488353 prefixEnd_1488353 764240472561320545742695 := by
  unfold tailWord_1488353
  simp only [CollatzResearch.WordTrace]
  refine ⟨54284693576958746300373713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36189795717972497533582475 54284693576958746300373713)
  ·
    refine ⟨40713520182719059725280285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54284693576958746300373713 40713520182719059725280285)
    ·
      refine ⟨15267570068519647396980107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40713520182719059725280285 15267570068519647396980107)
      ·
        refine ⟨22901355102779471095470161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15267570068519647396980107 22901355102779471095470161)
        ·
          refine ⟨17176016327084603321602621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22901355102779471095470161 17176016327084603321602621)
          ·
            refine ⟨6441006122656726245600983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17176016327084603321602621 6441006122656726245600983)
            ·
              refine ⟨9661509183985089368401475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6441006122656726245600983 9661509183985089368401475)
              ·
                refine ⟨14492263775977634052602213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9661509183985089368401475 14492263775977634052602213)
                ·
                  refine ⟨2717299457995806384862915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14492263775977634052602213 2717299457995806384862915)
                  ·
                    refine ⟨4075949186993709577294373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2717299457995806384862915 4075949186993709577294373)
                    ·
                      refine ⟨764240472561320545742695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4075949186993709577294373 764240472561320545742695)
                      ·
                        rfl

theorem cell23_1488353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 4, 1, 4].length) (baseStart_1488353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1488353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1488353 prefixEnd_1488353 := by exact prefixLift 1488353
  have htrace : WordTrace (prefixWord ++ tailWord_1488353) baseStart_1488353 baseEnd_1488353 := by
    simpa [prefixWord, tailWord_1488353, baseEnd_1488353] using wordTrace_append hprefix tailTrace_1488353
  have hstable : (prefixWord ++ tailWord_1488353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488353).length < 2 ^ (prefixWord ++ tailWord_1488353).sum := by decide
  have hdescent : baseEnd_1488353 < baseStart_1488353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488363 : List Nat := [1, 1, 1, 1, 2, 3, 2, 5, 3, 4]
def baseStart_1488363 : Nat := 118140960795 + 1488363 * 2 ^ 59
def prefixEnd_1488363 : Nat := 4983230072969 + 3 ^ 40 * 1488363 * 2
def baseEnd_1488363 : Nat := 254748535789288502205883

theorem tailTrace_1488363 : CollatzResearch.WordTrace tailWord_1488363 prefixEnd_1488363 254748535789288502205883 := by
  unfold tailWord_1488363
  simp only [CollatzResearch.WordTrace]
  refine ⟨54285058306922518008237743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36190038871281678672158495 54285058306922518008237743)
  ·
    refine ⟨81427587460383777012356615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54285058306922518008237743 81427587460383777012356615)
    ·
      refine ⟨122141381190575665518534923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81427587460383777012356615 122141381190575665518534923)
      ·
        refine ⟨183212071785863498277802385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122141381190575665518534923 183212071785863498277802385)
        ·
          refine ⟨137409053839397623708351789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183212071785863498277802385 137409053839397623708351789)
          ·
            refine ⟨51528395189774108890631921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137409053839397623708351789 51528395189774108890631921)
            ·
              refine ⟨38646296392330581667973941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51528395189774108890631921 38646296392330581667973941)
              ·
                refine ⟨3623090286780992031372557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38646296392330581667973941 3623090286780992031372557)
                ·
                  refine ⟨1358658857542872011764709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3623090286780992031372557 1358658857542872011764709)
                  ·
                    refine ⟨254748535789288502205883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1358658857542872011764709 254748535789288502205883)
                    ·
                      rfl

theorem cell23_1488363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5, 3, 4].length) (baseStart_1488363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1488363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1488363 prefixEnd_1488363 := by exact prefixLift 1488363
  have htrace : WordTrace (prefixWord ++ tailWord_1488363) baseStart_1488363 baseEnd_1488363 := by
    simpa [prefixWord, tailWord_1488363, baseEnd_1488363] using wordTrace_append hprefix tailTrace_1488363
  have hstable : (prefixWord ++ tailWord_1488363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488363).length < 2 ^ (prefixWord ++ tailWord_1488363).sum := by decide
  have hdescent : baseEnd_1488363 < baseStart_1488363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488413 : List Nat := [1, 4, 2, 2, 1, 1, 2, 1, 1, 2, 6]
def baseStart_1488413 : Nat := 118140960795 + 1488413 * 2 ^ 59
def prefixEnd_1488413 : Nat := 4983230072969 + 3 ^ 40 * 1488413 * 2
def baseEnd_1488413 : Nat := 764271281400590310992419

theorem tailTrace_1488413 : CollatzResearch.WordTrace tailWord_1488413 prefixEnd_1488413 764271281400590310992419 := by
  unfold tailWord_1488413
  simp only [CollatzResearch.WordTrace]
  refine ⟨54286881956741376547557893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36191254637827584365038595 54286881956741376547557893)
  ·
    refine ⟨10178790366889008102667105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54286881956741376547557893 10178790366889008102667105)
    ·
      refine ⟨7634092775166756077000329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10178790366889008102667105 7634092775166756077000329)
      ·
        refine ⟨5725569581375067057750247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7634092775166756077000329 5725569581375067057750247)
        ·
          refine ⟨8588354372062600586625371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5725569581375067057750247 8588354372062600586625371)
          ·
            refine ⟨12882531558093900879938057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8588354372062600586625371 12882531558093900879938057)
            ·
              refine ⟨9661898668570425659953543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12882531558093900879938057 9661898668570425659953543)
              ·
                refine ⟨14492848002855638489930315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9661898668570425659953543 14492848002855638489930315)
                ·
                  refine ⟨21739272004283457734895473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14492848002855638489930315 21739272004283457734895473)
                  ·
                    refine ⟨16304454003212593301171605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21739272004283457734895473 16304454003212593301171605)
                    ·
                      refine ⟨764271281400590310992419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16304454003212593301171605 764271281400590310992419)
                      ·
                        rfl

theorem cell23_1488413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_1488413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1488413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1488413 prefixEnd_1488413 := by exact prefixLift 1488413
  have htrace : WordTrace (prefixWord ++ tailWord_1488413) baseStart_1488413 baseEnd_1488413 := by
    simpa [prefixWord, tailWord_1488413, baseEnd_1488413] using wordTrace_append hprefix tailTrace_1488413
  have hstable : (prefixWord ++ tailWord_1488413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488413).length < 2 ^ (prefixWord ++ tailWord_1488413).sum := by decide
  have hdescent : baseEnd_1488413 < baseStart_1488413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488437 : List Nat := [1, 3, 3, 1, 1, 4, 1, 2, 3, 1, 3]
def baseStart_1488437 : Nat := 118140960795 + 1488437 * 2 ^ 59
def prefixEnd_1488437 : Nat := 4983230072969 + 3 ^ 40 * 1488437 * 2
def baseEnd_1488437 : Nat := 764283604936298217092309

theorem tailTrace_1488437 : CollatzResearch.WordTrace tailWord_1488437 prefixEnd_1488437 764283604936298217092309 := by
  unfold tailWord_1488437
  simp only [CollatzResearch.WordTrace]
  refine ⟨54287757308654428646431565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36191838205769619097621043 54287757308654428646431565)
  ·
    refine ⟨20357908990745410742411837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54287757308654428646431565 20357908990745410742411837)
    ·
      refine ⟨7634215871529529028404439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20357908990745410742411837 7634215871529529028404439)
      ·
        refine ⟨11451323807294293542606659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7634215871529529028404439 11451323807294293542606659)
        ·
          refine ⟨17176985710941440313909989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11451323807294293542606659 17176985710941440313909989)
          ·
            refine ⟨3220684820801520058858123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17176985710941440313909989 3220684820801520058858123)
            ·
              refine ⟨4831027231202280088287185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3220684820801520058858123 4831027231202280088287185)
              ·
                refine ⟨3623270423401710066215389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4831027231202280088287185 3623270423401710066215389)
                ·
                  refine ⟨1358726408775641274830771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3623270423401710066215389 1358726408775641274830771)
                  ·
                    refine ⟨2038089613163461912246157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1358726408775641274830771 2038089613163461912246157)
                    ·
                      refine ⟨764283604936298217092309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2038089613163461912246157 764283604936298217092309)
                      ·
                        rfl

theorem cell23_1488437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 2, 3, 1, 3].length) (baseStart_1488437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1488437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1488437 prefixEnd_1488437 := by exact prefixLift 1488437
  have htrace : WordTrace (prefixWord ++ tailWord_1488437) baseStart_1488437 baseEnd_1488437 := by
    simpa [prefixWord, tailWord_1488437, baseEnd_1488437] using wordTrace_append hprefix tailTrace_1488437
  have hstable : (prefixWord ++ tailWord_1488437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488437).length < 2 ^ (prefixWord ++ tailWord_1488437).sum := by decide
  have hdescent : baseEnd_1488437 < baseStart_1488437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488447 : List Nat := [1, 1, 2, 2, 3, 3, 3, 1, 2, 3, 2]
def baseStart_1488447 : Nat := 118140960795 + 1488447 * 2 ^ 59
def prefixEnd_1488447 : Nat := 4983230072969 + 3 ^ 40 * 1488447 * 2
def baseEnd_1488447 : Nat := 764288739742843177967263

theorem tailTrace_1488447 : CollatzResearch.WordTrace tailWord_1488447 prefixEnd_1488447 764288739742843177967263 := by
  unfold tailWord_1488447
  simp only [CollatzResearch.WordTrace]
  refine ⟨54288122038618200354295595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36192081359078800236197063 54288122038618200354295595)
  ·
    refine ⟨81432183057927300531443393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54288122038618200354295595 81432183057927300531443393)
    ·
      refine ⟨61074137293445475398582545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81432183057927300531443393 61074137293445475398582545)
      ·
        refine ⟨45805602970084106548936909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61074137293445475398582545 45805602970084106548936909)
        ·
          refine ⟨17177101113781539955851341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45805602970084106548936909 17177101113781539955851341)
          ·
            refine ⟨6441412917668077483444253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17177101113781539955851341 6441412917668077483444253)
            ·
              refine ⟨2415529844125529056291595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6441412917668077483444253 2415529844125529056291595)
              ·
                refine ⟨3623294766188293584437393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2415529844125529056291595 3623294766188293584437393)
                ·
                  refine ⟨2717471074641220188328045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3623294766188293584437393 2717471074641220188328045)
                  ·
                    refine ⟨1019051652990457570623017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2717471074641220188328045 1019051652990457570623017)
                    ·
                      refine ⟨764288739742843177967263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1019051652990457570623017 764288739742843177967263)
                      ·
                        rfl

theorem cell23_1488447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 1, 2, 3, 2].length) (baseStart_1488447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1488447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1488447 prefixEnd_1488447 := by exact prefixLift 1488447
  have htrace : WordTrace (prefixWord ++ tailWord_1488447) baseStart_1488447 baseEnd_1488447 := by
    simpa [prefixWord, tailWord_1488447, baseEnd_1488447] using wordTrace_append hprefix tailTrace_1488447
  have hstable : (prefixWord ++ tailWord_1488447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488447).length < 2 ^ (prefixWord ++ tailWord_1488447).sum := by decide
  have hdescent : baseEnd_1488447 < baseStart_1488447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488453 : List Nat := [1, 3, 1, 1, 1, 4, 1, 4, 1, 6]
def baseStart_1488453 : Nat := 118140960795 + 1488453 * 2 ^ 59
def prefixEnd_1488453 : Nat := 4983230072969 + 3 ^ 40 * 1488453 * 2
def baseEnd_1488453 : Nat := 254763940208923384830745

theorem tailTrace_1488453 : CollatzResearch.WordTrace tailWord_1488453 prefixEnd_1488453 254763940208923384830745 := by
  unfold tailWord_1488453
  simp only [CollatzResearch.WordTrace]
  refine ⟨54288340876596463379014013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36192227251064308919342675 54288340876596463379014013)
  ·
    refine ⟨20358127828723673767130255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54288340876596463379014013 20358127828723673767130255)
    ·
      refine ⟨30537191743085510650695383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20358127828723673767130255 30537191743085510650695383)
      ·
        refine ⟨45805787614628265976043075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30537191743085510650695383 45805787614628265976043075)
        ·
          refine ⟨68708681421942398964064613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45805787614628265976043075 68708681421942398964064613)
          ·
            refine ⟨12882877766614199805762115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68708681421942398964064613 12882877766614199805762115)
            ·
              refine ⟨19324316649921299708643173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12882877766614199805762115 19324316649921299708643173)
              ·
                refine ⟨3623309371860243695370595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19324316649921299708643173 3623309371860243695370595)
                ·
                  refine ⟨5434964057790365543055893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3623309371860243695370595 5434964057790365543055893)
                  ·
                    refine ⟨254763940208923384830745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5434964057790365543055893 254763940208923384830745)
                    ·
                      rfl

theorem cell23_1488453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4, 1, 6].length) (baseStart_1488453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1488453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1488453 prefixEnd_1488453 := by exact prefixLift 1488453
  have htrace : WordTrace (prefixWord ++ tailWord_1488453) baseStart_1488453 baseEnd_1488453 := by
    simpa [prefixWord, tailWord_1488453, baseEnd_1488453] using wordTrace_append hprefix tailTrace_1488453
  have hstable : (prefixWord ++ tailWord_1488453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488453).length < 2 ^ (prefixWord ++ tailWord_1488453).sum := by decide
  have hdescent : baseEnd_1488453 < baseStart_1488453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488463 : List Nat := [1, 1, 2, 1, 1, 2, 3, 5, 1, 1, 5]
def baseStart_1488463 : Nat := 118140960795 + 1488463 * 2 ^ 59
def prefixEnd_1488463 : Nat := 4983230072969 + 3 ^ 40 * 1488463 * 2
def baseEnd_1488463 : Nat := 764296955433315115367189

theorem tailTrace_1488463 : CollatzResearch.WordTrace tailWord_1488463 prefixEnd_1488463 764296955433315115367189 := by
  unfold tailWord_1488463
  simp only [CollatzResearch.WordTrace]
  refine ⟨54288705606560235086878043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36192470404373490057918695 54288705606560235086878043)
  ·
    refine ⟨81433058409840352630317065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54288705606560235086878043 81433058409840352630317065)
    ·
      refine ⟨61074793807380264472737799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81433058409840352630317065 61074793807380264472737799)
      ·
        refine ⟨91612190711070396709106699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61074793807380264472737799 91612190711070396709106699)
        ·
          refine ⟨137418286066605595063660049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91612190711070396709106699 137418286066605595063660049)
          ·
            refine ⟨103063714549954196297745037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137418286066605595063660049 103063714549954196297745037)
            ·
              refine ⟨38648892956232823611654389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103063714549954196297745037 38648892956232823611654389)
              ·
                refine ⟨3623333714646827213592599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38648892956232823611654389 3623333714646827213592599)
                ·
                  refine ⟨5435000571970240820388899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3623333714646827213592599 5435000571970240820388899)
                  ·
                    refine ⟨8152500857955361230583349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5435000571970240820388899 8152500857955361230583349)
                    ·
                      refine ⟨764296955433315115367189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8152500857955361230583349 764296955433315115367189)
                      ·
                        rfl

theorem cell23_1488463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5, 1, 1, 5].length) (baseStart_1488463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1488463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1488463 prefixEnd_1488463 := by exact prefixLift 1488463
  have htrace : WordTrace (prefixWord ++ tailWord_1488463) baseStart_1488463 baseEnd_1488463 := by
    simpa [prefixWord, tailWord_1488463, baseEnd_1488463] using wordTrace_append hprefix tailTrace_1488463
  have hstable : (prefixWord ++ tailWord_1488463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488463).length < 2 ^ (prefixWord ++ tailWord_1488463).sum := by decide
  have hdescent : baseEnd_1488463 < baseStart_1488463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488473 : List Nat := [1, 2, 1, 2, 2, 1, 1, 4, 3, 2, 4]
def baseStart_1488473 : Nat := 118140960795 + 1488473 * 2 ^ 59
def prefixEnd_1488473 : Nat := 4983230072969 + 3 ^ 40 * 1488473 * 2
def baseEnd_1488473 : Nat := 764302090239860076242143

theorem tailTrace_1488473 : CollatzResearch.WordTrace tailWord_1488473 prefixEnd_1488473 764302090239860076242143 := by
  unfold tailWord_1488473
  simp only [CollatzResearch.WordTrace]
  refine ⟨54289070336524006794742073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36192713557682671196494715 54289070336524006794742073)
  ·
    refine ⟨40716802752393005096056555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54289070336524006794742073 40716802752393005096056555)
    ·
      refine ⟨61075204128589507644084833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40716802752393005096056555 61075204128589507644084833)
      ·
        refine ⟨45806403096442130733063625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61075204128589507644084833 45806403096442130733063625)
        ·
          refine ⟨34354802322331598049797719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45806403096442130733063625 34354802322331598049797719)
          ·
            refine ⟨51532203483497397074696579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34354802322331598049797719 51532203483497397074696579)
            ·
              refine ⟨77298305225246095612044869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51532203483497397074696579 77298305225246095612044869)
              ·
                refine ⟨14493432229733642927258413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77298305225246095612044869 14493432229733642927258413)
                ·
                  refine ⟨5435037086150116097721905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14493432229733642927258413 5435037086150116097721905)
                  ·
                    refine ⟨4076277814612587073291429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5435037086150116097721905 4076277814612587073291429)
                    ·
                      refine ⟨764302090239860076242143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4076277814612587073291429 764302090239860076242143)
                      ·
                        rfl

theorem cell23_1488473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3, 2, 4].length) (baseStart_1488473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1488473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1488473 prefixEnd_1488473 := by exact prefixLift 1488473
  have htrace : WordTrace (prefixWord ++ tailWord_1488473) baseStart_1488473 baseEnd_1488473 := by
    simpa [prefixWord, tailWord_1488473, baseEnd_1488473] using wordTrace_append hprefix tailTrace_1488473
  have hstable : (prefixWord ++ tailWord_1488473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488473).length < 2 ^ (prefixWord ++ tailWord_1488473).sum := by decide
  have hdescent : baseEnd_1488473 < baseStart_1488473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488490 : List Nat := [3, 1, 3, 2, 1, 3, 1, 1, 1, 1, 6]
def baseStart_1488490 : Nat := 118140960795 + 1488490 * 2 ^ 59
def prefixEnd_1488490 : Nat := 4983230072969 + 3 ^ 40 * 1488490 * 2
def baseEnd_1488490 : Nat := 764310819410986509729565

theorem tailTrace_1488490 : CollatzResearch.WordTrace tailWord_1488490 prefixEnd_1488490 764310819410986509729565 := by
  unfold tailWord_1488490
  simp only [CollatzResearch.WordTrace]
  refine ⟨13572422594365604674527731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36193126918308279132073949 13572422594365604674527731)
  ·
    refine ⟨20358633891548407011791597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13572422594365604674527731 20358633891548407011791597)
    ·
      refine ⟨7634487709330652629421849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20358633891548407011791597 7634487709330652629421849)
      ·
        refine ⟨5725865781997989472066387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7634487709330652629421849 5725865781997989472066387)
        ·
          refine ⟨8588798672996984208099581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5725865781997989472066387 8588798672996984208099581)
          ·
            refine ⟨3220799502373869078037343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8588798672996984208099581 3220799502373869078037343)
            ·
              refine ⟨4831199253560803617056015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3220799502373869078037343 4831199253560803617056015)
              ·
                refine ⟨7246798880341205425584023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4831199253560803617056015 7246798880341205425584023)
                ·
                  refine ⟨10870198320511808138376035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7246798880341205425584023 10870198320511808138376035)
                  ·
                    refine ⟨16305297480767712207564053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10870198320511808138376035 16305297480767712207564053)
                    ·
                      refine ⟨764310819410986509729565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16305297480767712207564053 764310819410986509729565)
                      ·
                        rfl

theorem cell23_1488490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_1488490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1488490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1488490 prefixEnd_1488490 := by exact prefixLift 1488490
  have htrace : WordTrace (prefixWord ++ tailWord_1488490) baseStart_1488490 baseEnd_1488490 := by
    simpa [prefixWord, tailWord_1488490, baseEnd_1488490] using wordTrace_append hprefix tailTrace_1488490
  have hstable : (prefixWord ++ tailWord_1488490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488490).length < 2 ^ (prefixWord ++ tailWord_1488490).sum := by decide
  have hdescent : baseEnd_1488490 < baseStart_1488490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488494 : List Nat := [4, 1, 2, 2, 3, 1, 2, 2, 1, 1, 4]
def baseStart_1488494 : Nat := 118140960795 + 1488494 * 2 ^ 59
def prefixEnd_1488494 : Nat := 4983230072969 + 3 ^ 40 * 1488494 * 2
def baseEnd_1488494 : Nat := 764312873333604494079547

theorem tailTrace_1488494 : CollatzResearch.WordTrace tailWord_1488494 prefixEnd_1488494 764312873333604494079547 := by
  unfold tailWord_1488494
  simp only [CollatzResearch.WordTrace]
  refine ⟨6786229533680990922657067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36193224179631951587504357 6786229533680990922657067)
  ·
    refine ⟨10179344300521486383985601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6786229533680990922657067 10179344300521486383985601)
    ·
      refine ⟨7634508225391114787989201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10179344300521486383985601 7634508225391114787989201)
      ·
        refine ⟨5725881169043336090991901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7634508225391114787989201 5725881169043336090991901)
        ·
          refine ⟨2147205438391251034121963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5725881169043336090991901 2147205438391251034121963)
          ·
            refine ⟨3220808157586876551182945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2147205438391251034121963 3220808157586876551182945)
            ·
              refine ⟨2415606118190157413387209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3220808157586876551182945 2415606118190157413387209)
              ·
                refine ⟨1811704588642618060040407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2415606118190157413387209 1811704588642618060040407)
                ·
                  refine ⟨2717556882963927090060611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1811704588642618060040407 2717556882963927090060611)
                  ·
                    refine ⟨4076335324445890635090917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2717556882963927090060611 4076335324445890635090917)
                    ·
                      refine ⟨764312873333604494079547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4076335324445890635090917 764312873333604494079547)
                      ·
                        rfl

theorem cell23_1488494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_1488494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1488494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1488494 prefixEnd_1488494 := by exact prefixLift 1488494
  have htrace : WordTrace (prefixWord ++ tailWord_1488494) baseStart_1488494 baseEnd_1488494 := by
    simpa [prefixWord, tailWord_1488494, baseEnd_1488494] using wordTrace_append hprefix tailTrace_1488494
  have hstable : (prefixWord ++ tailWord_1488494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488494).length < 2 ^ (prefixWord ++ tailWord_1488494).sum := by decide
  have hdescent : baseEnd_1488494 < baseStart_1488494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488523 : List Nat := [1, 1, 1, 1, 4, 1, 3, 2, 2, 2, 5]
def baseStart_1488523 : Nat := 118140960795 + 1488523 * 2 ^ 59
def prefixEnd_1488523 : Nat := 4983230072969 + 3 ^ 40 * 1488523 * 2
def baseEnd_1488523 : Nat := 764327764272584880616913

theorem tailTrace_1488523 : CollatzResearch.WordTrace tailWord_1488523 prefixEnd_1488523 764327764272584880616913 := by
  unfold tailWord_1488523
  simp only [CollatzResearch.WordTrace]
  refine ⟨54290893986342865334062223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36193929324228576889374815 54290893986342865334062223)
  ·
    refine ⟨81436340979514298001093335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54290893986342865334062223 81436340979514298001093335)
    ·
      refine ⟨122154511469271447001640003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81436340979514298001093335 122154511469271447001640003)
      ·
        refine ⟨183231767203907170502460005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122154511469271447001640003 183231767203907170502460005)
        ·
          refine ⟨34355956350732594469211251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 183231767203907170502460005 34355956350732594469211251)
          ·
            refine ⟨51533934526098891703816877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34355956350732594469211251 51533934526098891703816877)
            ·
              refine ⟨19325225447287084388931329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51533934526098891703816877 19325225447287084388931329)
              ·
                refine ⟨14493919085465313291698497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19325225447287084388931329 14493919085465313291698497)
                ·
                  refine ⟨10870439314098984968773873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14493919085465313291698497 10870439314098984968773873)
                  ·
                    refine ⟨8152829485574238726580405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10870439314098984968773873 8152829485574238726580405)
                    ·
                      refine ⟨764327764272584880616913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8152829485574238726580405 764327764272584880616913)
                      ·
                        rfl

theorem cell23_1488523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2, 5].length) (baseStart_1488523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1488523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1488523 prefixEnd_1488523 := by exact prefixLift 1488523
  have htrace : WordTrace (prefixWord ++ tailWord_1488523) baseStart_1488523 baseEnd_1488523 := by
    simpa [prefixWord, tailWord_1488523, baseEnd_1488523] using wordTrace_append hprefix tailTrace_1488523
  have hstable : (prefixWord ++ tailWord_1488523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488523).length < 2 ^ (prefixWord ++ tailWord_1488523).sum := by decide
  have hdescent : baseEnd_1488523 < baseStart_1488523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488544 : List Nat := [2, 1, 1, 4, 3, 2, 1, 3, 2, 1, 3]
def baseStart_1488544 : Nat := 118140960795 + 1488544 * 2 ^ 59
def prefixEnd_1488544 : Nat := 4983230072969 + 3 ^ 40 * 1488544 * 2
def baseEnd_1488544 : Nat := 764338547366329298454317

theorem tailTrace_1488544 : CollatzResearch.WordTrace tailWord_1488544 prefixEnd_1488544 764338547366329298454317 := by
  unfold tailWord_1488544
  simp only [CollatzResearch.WordTrace]
  refine ⟨27145829959633392960288343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36194439946177857280384457 27145829959633392960288343)
  ·
    refine ⟨40718744939450089440432515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27145829959633392960288343 40718744939450089440432515)
    ·
      refine ⟨61078117409175134160648773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40718744939450089440432515 61078117409175134160648773)
      ·
        refine ⟨11452147014220337655121645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61078117409175134160648773 11452147014220337655121645)
        ·
          refine ⟨4294555130332626620670617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11452147014220337655121645 4294555130332626620670617)
          ·
            refine ⟨3220916347749469965502963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4294555130332626620670617 3220916347749469965502963)
            ·
              refine ⟨4831374521624204948254445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3220916347749469965502963 4831374521624204948254445)
              ·
                refine ⟨1811765445609076855595417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4831374521624204948254445 1811765445609076855595417)
                ·
                  refine ⟨1358824084206807641696563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1811765445609076855595417 1358824084206807641696563)
                  ·
                    refine ⟨2038236126310211462544845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1358824084206807641696563 2038236126310211462544845)
                    ·
                      refine ⟨764338547366329298454317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2038236126310211462544845 764338547366329298454317)
                      ·
                        rfl

theorem cell23_1488544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 3, 2, 1, 3].length) (baseStart_1488544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1488544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1488544 prefixEnd_1488544 := by exact prefixLift 1488544
  have htrace : WordTrace (prefixWord ++ tailWord_1488544) baseStart_1488544 baseEnd_1488544 := by
    simpa [prefixWord, tailWord_1488544, baseEnd_1488544] using wordTrace_append hprefix tailTrace_1488544
  have hstable : (prefixWord ++ tailWord_1488544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488544).length < 2 ^ (prefixWord ++ tailWord_1488544).sum := by decide
  have hdescent : baseEnd_1488544 < baseStart_1488544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488567 : List Nat := [1, 1, 3, 1, 5, 1, 1, 1, 3, 4, 2]
def baseStart_1488567 : Nat := 118140960795 + 1488567 * 2 ^ 59
def prefixEnd_1488567 : Nat := 4983230072969 + 3 ^ 40 * 1488567 * 2
def baseEnd_1488567 : Nat := 764350357421382708466711

theorem tailTrace_1488567 : CollatzResearch.WordTrace tailWord_1488567 prefixEnd_1488567 764350357421382708466711 := by
  unfold tailWord_1488567
  simp only [CollatzResearch.WordTrace]
  refine ⟨54292498798183460848663955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36194999198788973899109303 54292498798183460848663955)
  ·
    refine ⟨81438748197275191272995933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54292498798183460848663955 81438748197275191272995933)
    ·
      refine ⟨30539530573978196727373475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81438748197275191272995933 30539530573978196727373475)
      ·
        refine ⟨45809295860967295091060213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30539530573978196727373475 45809295860967295091060213)
        ·
          refine ⟨4294621486965683914786895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45809295860967295091060213 4294621486965683914786895)
          ·
            refine ⟨6441932230448525872180343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4294621486965683914786895 6441932230448525872180343)
            ·
              refine ⟨9662898345672788808270515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6441932230448525872180343 9662898345672788808270515)
              ·
                refine ⟨14494347518509183212405773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9662898345672788808270515 14494347518509183212405773)
                ·
                  refine ⟨5435380319440943704652165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14494347518509183212405773 5435380319440943704652165)
                  ·
                    refine ⟨1019133809895176944622281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5435380319440943704652165 1019133809895176944622281)
                    ·
                      refine ⟨764350357421382708466711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1019133809895176944622281 764350357421382708466711)
                      ·
                        rfl

theorem cell23_1488567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 3, 4, 2].length) (baseStart_1488567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1488567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1488567 prefixEnd_1488567 := by exact prefixLift 1488567
  have htrace : WordTrace (prefixWord ++ tailWord_1488567) baseStart_1488567 baseEnd_1488567 := by
    simpa [prefixWord, tailWord_1488567, baseEnd_1488567] using wordTrace_append hprefix tailTrace_1488567
  have hstable : (prefixWord ++ tailWord_1488567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488567).length < 2 ^ (prefixWord ++ tailWord_1488567).sum := by decide
  have hdescent : baseEnd_1488567 < baseStart_1488567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488570 : List Nat := [3, 1, 1, 1, 2, 4, 2, 1, 2, 1, 5]
def baseStart_1488570 : Nat := 118140960795 + 1488570 * 2 ^ 59
def prefixEnd_1488570 : Nat := 4983230072969 + 3 ^ 40 * 1488570 * 2
def baseEnd_1488570 : Nat := 764351897863346196729197

theorem tailTrace_1488570 : CollatzResearch.WordTrace tailWord_1488570 prefixEnd_1488570 764351897863346196729197 := by
  unfold tailWord_1488570
  simp only [CollatzResearch.WordTrace]
  refine ⟨13573152054293148090255791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36195072144781728240682109 13573152054293148090255791)
  ·
    refine ⟨20359728081439722135383687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13573152054293148090255791 20359728081439722135383687)
    ·
      refine ⟨30539592122159583203075531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20359728081439722135383687 30539592122159583203075531)
      ·
        refine ⟨45809388183239374804613297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30539592122159583203075531 45809388183239374804613297)
        ·
          refine ⟨34357041137429531103459973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45809388183239374804613297 34357041137429531103459973)
          ·
            refine ⟨6441945213268037081898745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34357041137429531103459973 6441945213268037081898745)
            ·
              refine ⟨4831458909951027811424059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6441945213268037081898745 4831458909951027811424059)
              ·
                refine ⟨7247188364926541717136089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4831458909951027811424059 7247188364926541717136089)
                ·
                  refine ⟨5435391273694906287852067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7247188364926541717136089 5435391273694906287852067)
                  ·
                    refine ⟨8153086910542359431778101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5435391273694906287852067 8153086910542359431778101)
                    ·
                      refine ⟨764351897863346196729197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8153086910542359431778101 764351897863346196729197)
                      ·
                        rfl

theorem cell23_1488570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 2, 1, 5].length) (baseStart_1488570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1488570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1488570 prefixEnd_1488570 := by exact prefixLift 1488570
  have htrace : WordTrace (prefixWord ++ tailWord_1488570) baseStart_1488570 baseEnd_1488570 := by
    simpa [prefixWord, tailWord_1488570, baseEnd_1488570] using wordTrace_append hprefix tailTrace_1488570
  have hstable : (prefixWord ++ tailWord_1488570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488570).length < 2 ^ (prefixWord ++ tailWord_1488570).sum := by decide
  have hdescent : baseEnd_1488570 < baseStart_1488570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488590 : List Nat := [4, 1, 1, 1, 3, 1, 2, 3, 7]
def baseStart_1488590 : Nat := 118140960795 + 1488590 * 2 ^ 59
def prefixEnd_1488590 : Nat := 4983230072969 + 3 ^ 40 * 1488590 * 2
def baseEnd_1488590 : Nat := 84929129719604013164345

theorem tailTrace_1488590 : CollatzResearch.WordTrace tailWord_1488590 prefixEnd_1488590 84929129719604013164345 := by
  unfold tailWord_1488590
  simp only [CollatzResearch.WordTrace]
  refine ⟨6786667209637516972093903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36195558451400090517834149 6786667209637516972093903)
  ·
    refine ⟨10180000814456275458140855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6786667209637516972093903 10180000814456275458140855)
    ·
      refine ⟨15270001221684413187211283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10180000814456275458140855 15270001221684413187211283)
      ·
        refine ⟨22905001832526619780816925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15270001221684413187211283 22905001832526619780816925)
        ·
          refine ⟨8589375687197482417806347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22905001832526619780816925 8589375687197482417806347)
          ·
            refine ⟨12884063530796223626709521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8589375687197482417806347 12884063530796223626709521)
            ·
              refine ⟨9663047648097167720032141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12884063530796223626709521 9663047648097167720032141)
              ·
                refine ⟨3623642868036437895012053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9663047648097167720032141 3623642868036437895012053)
                ·
                  refine ⟨84929129719604013164345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3623642868036437895012053 84929129719604013164345)
                  ·
                    rfl

theorem cell23_1488590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3, 7].length) (baseStart_1488590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1488590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1488590 prefixEnd_1488590 := by exact prefixLift 1488590
  have htrace : WordTrace (prefixWord ++ tailWord_1488590) baseStart_1488590 baseEnd_1488590 := by
    simpa [prefixWord, tailWord_1488590, baseEnd_1488590] using wordTrace_append hprefix tailTrace_1488590
  have hstable : (prefixWord ++ tailWord_1488590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488590).length < 2 ^ (prefixWord ++ tailWord_1488590).sum := by decide
  have hdescent : baseEnd_1488590 < baseStart_1488590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488677 : List Nat := [1, 3, 1, 2, 3, 2, 2, 1, 1, 4, 3]
def baseStart_1488677 : Nat := 118140960795 + 1488677 * 2 ^ 59
def prefixEnd_1488677 : Nat := 4983230072969 + 3 ^ 40 * 1488677 * 2
def baseEnd_1488677 : Nat := 764406840293377278091205

theorem tailTrace_1488677 : CollatzResearch.WordTrace tailWord_1488677 prefixEnd_1488677 764406840293377278091205 := by
  unfold tailWord_1488677
  simp only [CollatzResearch.WordTrace]
  refine ⟨54296510827784949635168285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36197673885189966423445523 54296510827784949635168285)
  ·
    refine ⟨20361191560419356113188107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54296510827784949635168285 20361191560419356113188107)
    ·
      refine ⟨30541787340629034169782161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20361191560419356113188107 30541787340629034169782161)
      ·
        refine ⟨22906340505471775627336621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30541787340629034169782161 22906340505471775627336621)
        ·
          refine ⟨8589877689551915860251233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22906340505471775627336621 8589877689551915860251233)
          ·
            refine ⟨6442408267163936895188425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8589877689551915860251233 6442408267163936895188425)
            ·
              refine ⟨4831806200372952671391319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6442408267163936895188425 4831806200372952671391319)
              ·
                refine ⟨7247709300559429007086979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4831806200372952671391319 7247709300559429007086979)
                ·
                  refine ⟨10871563950839143510630469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7247709300559429007086979 10871563950839143510630469)
                  ·
                    refine ⟨2038418240782339408243213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10871563950839143510630469 2038418240782339408243213)
                    ·
                      refine ⟨764406840293377278091205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2038418240782339408243213 764406840293377278091205)
                      ·
                        rfl

theorem cell23_1488677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 4, 3].length) (baseStart_1488677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1488677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1488677 prefixEnd_1488677 := by exact prefixLift 1488677
  have htrace : WordTrace (prefixWord ++ tailWord_1488677) baseStart_1488677 baseEnd_1488677 := by
    simpa [prefixWord, tailWord_1488677, baseEnd_1488677] using wordTrace_append hprefix tailTrace_1488677
  have hstable : (prefixWord ++ tailWord_1488677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488677).length < 2 ^ (prefixWord ++ tailWord_1488677).sum := by decide
  have hdescent : baseEnd_1488677 < baseStart_1488677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488700 : List Nat := [2, 2, 2, 2, 1, 1, 2, 1, 1, 1, 8]
def baseStart_1488700 : Nat := 118140960795 + 1488700 * 2 ^ 59
def prefixEnd_1488700 : Nat := 4983230072969 + 3 ^ 40 * 1488700 * 2
def baseEnd_1488700 : Nat := 764418650348430688103599

theorem tailTrace_1488700 : CollatzResearch.WordTrace tailWord_1488700 prefixEnd_1488700 764418650348430688103599 := by
  unfold tailWord_1488700
  simp only [CollatzResearch.WordTrace]
  refine ⟨27148674853350812281627777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36198233137801083042170369 27148674853350812281627777)
  ·
    refine ⟨20361506140013109211220833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27148674853350812281627777 20361506140013109211220833)
    ·
      refine ⟨15271129605009831908415625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20361506140013109211220833 15271129605009831908415625)
      ·
        refine ⟨11453347203757373931311719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15271129605009831908415625 11453347203757373931311719)
        ·
          refine ⟨17180020805636060896967579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11453347203757373931311719 17180020805636060896967579)
          ·
            refine ⟨25770031208454091345451369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17180020805636060896967579 25770031208454091345451369)
            ·
              refine ⟨19327523406340568509088527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25770031208454091345451369 19327523406340568509088527)
              ·
                refine ⟨28991285109510852763632791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19327523406340568509088527 28991285109510852763632791)
                ·
                  refine ⟨43486927664266279145449187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28991285109510852763632791 43486927664266279145449187)
                  ·
                    refine ⟨65230391496399418718173781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43486927664266279145449187 65230391496399418718173781)
                    ·
                      refine ⟨764418650348430688103599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 65230391496399418718173781 764418650348430688103599)
                      ·
                        rfl

theorem cell23_1488700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_1488700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1488700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1488700 prefixEnd_1488700 := by exact prefixLift 1488700
  have htrace : WordTrace (prefixWord ++ tailWord_1488700) baseStart_1488700 baseEnd_1488700 := by
    simpa [prefixWord, tailWord_1488700, baseEnd_1488700] using wordTrace_append hprefix tailTrace_1488700
  have hstable : (prefixWord ++ tailWord_1488700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488700).length < 2 ^ (prefixWord ++ tailWord_1488700).sum := by decide
  have hdescent : baseEnd_1488700 < baseStart_1488700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488701 : List Nat := [1, 4, 1, 4, 1, 3, 1, 1, 3, 4]
def baseStart_1488701 : Nat := 118140960795 + 1488701 * 2 ^ 59
def prefixEnd_1488701 : Nat := 4983230072969 + 3 ^ 40 * 1488701 * 2
def baseEnd_1488701 : Nat := 254806387943028394730365

theorem tailTrace_1488701 : CollatzResearch.WordTrace tailWord_1488701 prefixEnd_1488701 254806387943028394730365 := by
  unfold tailWord_1488701
  simp only [CollatzResearch.WordTrace]
  refine ⟨54297386179698001734041957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36198257453132001156027971 54297386179698001734041957)
  ·
    refine ⟨10180759908693375325132867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54297386179698001734041957 10180759908693375325132867)
    ·
      refine ⟨15271139863040062987699301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10180759908693375325132867 15271139863040062987699301)
      ·
        refine ⟨2863338724320011810193619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15271139863040062987699301 2863338724320011810193619)
        ·
          refine ⟨4295008086480017715290429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2863338724320011810193619 4295008086480017715290429)
          ·
            refine ⟨1610628032430006643233911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4295008086480017715290429 1610628032430006643233911)
            ·
              refine ⟨2415942048645009964850867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1610628032430006643233911 2415942048645009964850867)
              ·
                refine ⟨3623913072967514947276301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2415942048645009964850867 3623913072967514947276301)
                ·
                  refine ⟨1358967402362818105228613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3623913072967514947276301 1358967402362818105228613)
                  ·
                    refine ⟨254806387943028394730365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1358967402362818105228613 254806387943028394730365)
                    ·
                      rfl

theorem cell23_1488701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 1, 3, 4].length) (baseStart_1488701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1488701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1488701 prefixEnd_1488701 := by exact prefixLift 1488701
  have htrace : WordTrace (prefixWord ++ tailWord_1488701) baseStart_1488701 baseEnd_1488701 := by
    simpa [prefixWord, tailWord_1488701, baseEnd_1488701] using wordTrace_append hprefix tailTrace_1488701
  have hstable : (prefixWord ++ tailWord_1488701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488701).length < 2 ^ (prefixWord ++ tailWord_1488701).sum := by decide
  have hdescent : baseEnd_1488701 < baseStart_1488701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488741 : List Nat := [1, 3, 1, 3, 1, 1, 1, 7, 1, 1, 3]
def baseStart_1488741 : Nat := 118140960795 + 1488741 * 2 ^ 59
def prefixEnd_1488741 : Nat := 4983230072969 + 3 ^ 40 * 1488741 * 2
def baseEnd_1488741 : Nat := 764439703055265027690911

theorem tailTrace_1488741 : CollatzResearch.WordTrace tailWord_1488741 prefixEnd_1488741 764439703055265027690911 := by
  unfold tailWord_1488741
  simp only [CollatzResearch.WordTrace]
  refine ⟨54298845099553088565498077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36199230066368725710332051 54298845099553088565498077)
  ·
    refine ⟨20362066912332408212061779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54298845099553088565498077 20362066912332408212061779)
    ·
      refine ⟨30543100368498612318092669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20362066912332408212061779 30543100368498612318092669)
      ·
        refine ⟨11453662638186979619284751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30543100368498612318092669 11453662638186979619284751)
        ·
          refine ⟨17180493957280469428927127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11453662638186979619284751 17180493957280469428927127)
          ·
            refine ⟨25770740935920704143390691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17180493957280469428927127 25770740935920704143390691)
            ·
              refine ⟨38656111403881056215086037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25770740935920704143390691 38656111403881056215086037)
              ·
                refine ⟨906002611028462255041079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 38656111403881056215086037 906002611028462255041079)
                ·
                  refine ⟨1359003916542693382561619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 906002611028462255041079 1359003916542693382561619)
                  ·
                    refine ⟨2038505874814040073842429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1359003916542693382561619 2038505874814040073842429)
                    ·
                      refine ⟨764439703055265027690911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2038505874814040073842429 764439703055265027690911)
                      ·
                        rfl

theorem cell23_1488741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 7, 1, 1, 3].length) (baseStart_1488741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1488741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1488741 prefixEnd_1488741 := by exact prefixLift 1488741
  have htrace : WordTrace (prefixWord ++ tailWord_1488741) baseStart_1488741 baseEnd_1488741 := by
    simpa [prefixWord, tailWord_1488741, baseEnd_1488741] using wordTrace_append hprefix tailTrace_1488741
  have hstable : (prefixWord ++ tailWord_1488741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488741).length < 2 ^ (prefixWord ++ tailWord_1488741).sum := by decide
  have hdescent : baseEnd_1488741 < baseStart_1488741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488757 : List Nat := [1, 3, 4, 1, 1, 1, 1, 2, 3, 6]
def baseStart_1488757 : Nat := 118140960795 + 1488757 * 2 ^ 59
def prefixEnd_1488757 : Nat := 4983230072969 + 3 ^ 40 * 1488757 * 2
def baseEnd_1488757 : Nat := 254815972915245655030279

theorem tailTrace_1488757 : CollatzResearch.WordTrace tailWord_1488757 prefixEnd_1488757 254815972915245655030279 := by
  unfold tailWord_1488757
  simp only [CollatzResearch.WordTrace]
  refine ⟨54299428667495123298080525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36199619111663415532053683 54299428667495123298080525)
  ·
    refine ⟨20362285750310671236780197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54299428667495123298080525 20362285750310671236780197)
    ·
      refine ⟨3817928578183250856896287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20362285750310671236780197 3817928578183250856896287)
      ·
        refine ⟨5726892867274876285344431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3817928578183250856896287 5726892867274876285344431)
        ·
          refine ⟨8590339300912314428016647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5726892867274876285344431 8590339300912314428016647)
          ·
            refine ⟨12885508951368471642024971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8590339300912314428016647 12885508951368471642024971)
            ·
              refine ⟨19328263427052707463037457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12885508951368471642024971 19328263427052707463037457)
              ·
                refine ⟨14496197570289530597278093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19328263427052707463037457 14496197570289530597278093)
                ·
                  refine ⟨5436074088858573973979285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14496197570289530597278093 5436074088858573973979285)
                  ·
                    refine ⟨254815972915245655030279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5436074088858573973979285 254815972915245655030279)
                    ·
                      rfl

theorem cell23_1488757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_1488757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1488757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1488757 prefixEnd_1488757 := by exact prefixLift 1488757
  have htrace : WordTrace (prefixWord ++ tailWord_1488757) baseStart_1488757 baseEnd_1488757 := by
    simpa [prefixWord, tailWord_1488757, baseEnd_1488757] using wordTrace_append hprefix tailTrace_1488757
  have hstable : (prefixWord ++ tailWord_1488757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488757).length < 2 ^ (prefixWord ++ tailWord_1488757).sum := by decide
  have hdescent : baseEnd_1488757 < baseStart_1488757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488794 : List Nat := [3, 1, 1, 4, 2, 1, 2, 2, 1, 2, 4]
def baseStart_1488794 : Nat := 118140960795 + 1488794 * 2 ^ 59
def prefixEnd_1488794 : Nat := 4983230072969 + 3 ^ 40 * 1488794 * 2
def baseEnd_1488794 : Nat := 764466917529953320328167

theorem tailTrace_1488794 : CollatzResearch.WordTrace tailWord_1488794 prefixEnd_1488794 764466917529953320328167 := by
  unfold tailWord_1488794
  simp only [CollatzResearch.WordTrace]
  refine ⟨13575194542090269654294359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36200518778907385744784957 13575194542090269654294359)
  ·
    refine ⟨20362791813135404481441539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13575194542090269654294359 20362791813135404481441539)
    ·
      refine ⟨30544187719703106722162309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20362791813135404481441539 30544187719703106722162309)
      ·
        refine ⟨5727035197444332510405433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30544187719703106722162309 5727035197444332510405433)
        ·
          refine ⟨4295276398083249382804075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5727035197444332510405433 4295276398083249382804075)
          ·
            refine ⟨6442914597124874074206113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4295276398083249382804075 6442914597124874074206113)
            ·
              refine ⟨4832185947843655555654585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6442914597124874074206113 4832185947843655555654585)
              ·
                refine ⟨3624139460882741666740939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4832185947843655555654585 3624139460882741666740939)
                ·
                  refine ⟨5436209191324112500111409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3624139460882741666740939 5436209191324112500111409)
                  ·
                    refine ⟨4077156893493084375083557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5436209191324112500111409 4077156893493084375083557)
                    ·
                      refine ⟨764466917529953320328167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4077156893493084375083557 764466917529953320328167)
                      ·
                        rfl

theorem cell23_1488794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_1488794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1488794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1488794 prefixEnd_1488794 := by exact prefixLift 1488794
  have htrace : WordTrace (prefixWord ++ tailWord_1488794) baseStart_1488794 baseEnd_1488794 := by
    simpa [prefixWord, tailWord_1488794, baseEnd_1488794] using wordTrace_append hprefix tailTrace_1488794
  have hstable : (prefixWord ++ tailWord_1488794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488794).length < 2 ^ (prefixWord ++ tailWord_1488794).sum := by decide
  have hdescent : baseEnd_1488794 < baseStart_1488794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488808 : List Nat := [2, 1, 6, 2, 1, 1, 1, 1, 4, 4]
def baseStart_1488808 : Nat := 118140960795 + 1488808 * 2 ^ 59
def prefixEnd_1488808 : Nat := 4983230072969 + 3 ^ 40 * 1488808 * 2
def baseEnd_1488808 : Nat := 254824702086372088517701

theorem tailTrace_1488808 : CollatzResearch.WordTrace tailWord_1488808 prefixEnd_1488808 254824702086372088517701 := by
  unfold tailWord_1488808
  simp only [CollatzResearch.WordTrace]
  refine ⟨27150644395155179504093539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36200859193540239338791385 27150644395155179504093539)
  ·
    refine ⟨40725966592732769256140309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27150644395155179504093539 40725966592732769256140309)
    ·
      refine ⟨1909029684034348558881577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 40725966592732769256140309 1909029684034348558881577)
      ·
        refine ⟨1431772263025761419161183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1909029684034348558881577 1431772263025761419161183)
        ·
          refine ⟨2147658394538642128741775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1431772263025761419161183 2147658394538642128741775)
          ·
            refine ⟨3221487591807963193112663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2147658394538642128741775 3221487591807963193112663)
            ·
              refine ⟨4832231387711944789668995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3221487591807963193112663 4832231387711944789668995)
              ·
                refine ⟨7248347081567917184503493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4832231387711944789668995 7248347081567917184503493)
                ·
                  refine ⟨1359065077793984472094405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7248347081567917184503493 1359065077793984472094405)
                  ·
                    refine ⟨254824702086372088517701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1359065077793984472094405 254824702086372088517701)
                    ·
                      rfl

theorem cell23_1488808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_1488808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1488808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1488808 prefixEnd_1488808 := by exact prefixLift 1488808
  have htrace : WordTrace (prefixWord ++ tailWord_1488808) baseStart_1488808 baseEnd_1488808 := by
    simpa [prefixWord, tailWord_1488808, baseEnd_1488808] using wordTrace_append hprefix tailTrace_1488808
  have hstable : (prefixWord ++ tailWord_1488808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488808).length < 2 ^ (prefixWord ++ tailWord_1488808).sum := by decide
  have hdescent : baseEnd_1488808 < baseStart_1488808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488828 : List Nat := [2, 2, 2, 5, 1, 2, 1, 1, 1, 2, 4]
def baseStart_1488828 : Nat := 118140960795 + 1488828 * 2 ^ 59
def prefixEnd_1488828 : Nat := 4983230072969 + 3 ^ 40 * 1488828 * 2
def baseEnd_1488828 : Nat := 764484375872206187303011

theorem tailTrace_1488828 : CollatzResearch.WordTrace tailWord_1488828 prefixEnd_1488828 764484375872206187303011 := by
  unfold tailWord_1488828
  simp only [CollatzResearch.WordTrace]
  refine ⟨27151009125118951211957569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36201345500158601615943425 27151009125118951211957569)
  ·
    refine ⟨20363256843839213408968177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27151009125118951211957569 20363256843839213408968177)
    ·
      refine ⟨15272442632879410056726133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20363256843839213408968177 15272442632879410056726133)
      ·
        refine ⟨1431791496832444692818075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15272442632879410056726133 1431791496832444692818075)
        ·
          refine ⟨2147687245248667039227113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1431791496832444692818075 2147687245248667039227113)
          ·
            refine ⟨1610765433936500279420335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2147687245248667039227113 1610765433936500279420335)
            ·
              refine ⟨2416148150904750419130503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1610765433936500279420335 2416148150904750419130503)
              ·
                refine ⟨3624222226357125628695755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2416148150904750419130503 3624222226357125628695755)
                ·
                  refine ⟨5436333339535688443043633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3624222226357125628695755 5436333339535688443043633)
                  ·
                    refine ⟨4077250004651766332282725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5436333339535688443043633 4077250004651766332282725)
                    ·
                      refine ⟨764484375872206187303011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4077250004651766332282725 764484375872206187303011)
                      ·
                        rfl

theorem cell23_1488828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_1488828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1488828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1488828 prefixEnd_1488828 := by exact prefixLift 1488828
  have htrace : WordTrace (prefixWord ++ tailWord_1488828) baseStart_1488828 baseEnd_1488828 := by
    simpa [prefixWord, tailWord_1488828, baseEnd_1488828] using wordTrace_append hprefix tailTrace_1488828
  have hstable : (prefixWord ++ tailWord_1488828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488828).length < 2 ^ (prefixWord ++ tailWord_1488828).sum := by decide
  have hdescent : baseEnd_1488828 < baseStart_1488828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488874 : List Nat := [3, 1, 3, 1, 2, 1, 2, 1, 2, 4, 3]
def baseStart_1488874 : Nat := 118140960795 + 1488874 * 2 ^ 59
def prefixEnd_1488874 : Nat := 4983230072969 + 3 ^ 40 * 1488874 * 2
def baseEnd_1488874 : Nat := 764507995982313007327799

theorem tailTrace_1488874 : CollatzResearch.WordTrace tailWord_1488874 prefixEnd_1488874 764507995982313007327799 := by
  unfold tailWord_1488874
  simp only [CollatzResearch.WordTrace]
  refine ⟨13575924002017813070022419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36202464005380834853393117 13575924002017813070022419)
  ·
    refine ⟨20363886003026719605033629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13575924002017813070022419 20363886003026719605033629)
    ·
      refine ⟨7636457251135019851887611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20363886003026719605033629 7636457251135019851887611)
      ·
        refine ⟨11454685876702529777831417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7636457251135019851887611 11454685876702529777831417)
        ·
          refine ⟨8591014407526897333373563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11454685876702529777831417 8591014407526897333373563)
          ·
            refine ⟨12886521611290346000060345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8591014407526897333373563 12886521611290346000060345)
            ·
              refine ⟨9664891208467759500045259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12886521611290346000060345 9664891208467759500045259)
              ·
                refine ⟨14497336812701639250067889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9664891208467759500045259 14497336812701639250067889)
                ·
                  refine ⟨10873002609526229437550917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14497336812701639250067889 10873002609526229437550917)
                  ·
                    refine ⟨2038687989286168019540797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10873002609526229437550917 2038687989286168019540797)
                    ·
                      refine ⟨764507995982313007327799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2038687989286168019540797 764507995982313007327799)
                      ·
                        rfl

theorem cell23_1488874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_1488874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1488874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1488874 prefixEnd_1488874 := by exact prefixLift 1488874
  have htrace : WordTrace (prefixWord ++ tailWord_1488874) baseStart_1488874 baseEnd_1488874 := by
    simpa [prefixWord, tailWord_1488874, baseEnd_1488874] using wordTrace_append hprefix tailTrace_1488874
  have hstable : (prefixWord ++ tailWord_1488874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488874).length < 2 ^ (prefixWord ++ tailWord_1488874).sum := by decide
  have hdescent : baseEnd_1488874 < baseStart_1488874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488961 : List Nat := [1, 2, 5, 1, 2, 2, 1, 1, 1, 3, 4]
def baseStart_1488961 : Nat := 118140960795 + 1488961 * 2 ^ 59
def prefixEnd_1488961 : Nat := 4983230072969 + 3 ^ 40 * 1488961 * 2
def baseEnd_1488961 : Nat := 764552668799254166939899

theorem tailTrace_1488961 : CollatzResearch.WordTrace tailWord_1488961 prefixEnd_1488961 764552668799254166939899 := by
  unfold tailWord_1488961
  simp only [CollatzResearch.WordTrace]
  refine ⟨54306869158756066138506737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36204579439170710759004491 54306869158756066138506737)
  ·
    refine ⟨40730151869067049603880053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54306869158756066138506737 40730151869067049603880053)
    ·
      refine ⟨3818451737725035900363755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40730151869067049603880053 3818451737725035900363755)
      ·
        refine ⟨5727677606587553850545633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3818451737725035900363755 5727677606587553850545633)
        ·
          refine ⟨4295758204940665387909225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5727677606587553850545633 4295758204940665387909225)
          ·
            refine ⟨3221818653705499040931919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4295758204940665387909225 3221818653705499040931919)
            ·
              refine ⟨4832727980558248561397879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3221818653705499040931919 4832727980558248561397879)
              ·
                refine ⟨7249091970837372842096819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4832727980558248561397879 7249091970837372842096819)
                ·
                  refine ⟨10873637956256059263145229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7249091970837372842096819 10873637956256059263145229)
                  ·
                    refine ⟨4077614233596022223679461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10873637956256059263145229 4077614233596022223679461)
                    ·
                      refine ⟨764552668799254166939899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4077614233596022223679461 764552668799254166939899)
                      ·
                        rfl

theorem cell23_1488961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_1488961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1488961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1488961 prefixEnd_1488961 := by exact prefixLift 1488961
  have htrace : WordTrace (prefixWord ++ tailWord_1488961) baseStart_1488961 baseEnd_1488961 := by
    simpa [prefixWord, tailWord_1488961, baseEnd_1488961] using wordTrace_append hprefix tailTrace_1488961
  have hstable : (prefixWord ++ tailWord_1488961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488961).length < 2 ^ (prefixWord ++ tailWord_1488961).sum := by decide
  have hdescent : baseEnd_1488961 < baseStart_1488961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488974 : List Nat := [4, 1, 1, 1, 1, 4, 1, 1, 2, 1, 6]
def baseStart_1488974 : Nat := 118140960795 + 1488974 * 2 ^ 59
def prefixEnd_1488974 : Nat := 4983230072969 + 3 ^ 40 * 1488974 * 2
def baseEnd_1488974 : Nat := 764559344047762616077339

theorem tailTrace_1488974 : CollatzResearch.WordTrace tailWord_1488974 prefixEnd_1488974 764559344047762616077339 := by
  unfold tailWord_1488974
  simp only [CollatzResearch.WordTrace]
  refine ⟨6788417913463621169841247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36204895538472646239153317 6788417913463621169841247)
  ·
    refine ⟨10182626870195431754761871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6788417913463621169841247 10182626870195431754761871)
    ·
      refine ⟨15273940305293147632142807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10182626870195431754761871 15273940305293147632142807)
      ·
        refine ⟨22910910457939721448214211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15273940305293147632142807 22910910457939721448214211)
        ·
          refine ⟨34366365686909582172321317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22910910457939721448214211 34366365686909582172321317)
          ·
            refine ⟨6443693566295546657310247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34366365686909582172321317 6443693566295546657310247)
            ·
              refine ⟨9665540349443319985965371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6443693566295546657310247 9665540349443319985965371)
              ·
                refine ⟨14498310524164979978948057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9665540349443319985965371 14498310524164979978948057)
                ·
                  refine ⟨10873732893123734984211043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14498310524164979978948057 10873732893123734984211043)
                  ·
                    refine ⟨16310599339685602476316565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10873732893123734984211043 16310599339685602476316565)
                    ·
                      refine ⟨764559344047762616077339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16310599339685602476316565 764559344047762616077339)
                      ·
                        rfl

theorem cell23_1488974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_1488974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1488974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1488974 prefixEnd_1488974 := by exact prefixLift 1488974
  have htrace : WordTrace (prefixWord ++ tailWord_1488974) baseStart_1488974 baseEnd_1488974 := by
    simpa [prefixWord, tailWord_1488974, baseEnd_1488974] using wordTrace_append hprefix tailTrace_1488974
  have hstable : (prefixWord ++ tailWord_1488974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488974).length < 2 ^ (prefixWord ++ tailWord_1488974).sum := by decide
  have hdescent : baseEnd_1488974 < baseStart_1488974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488984 : List Nat := [2, 1, 2, 2, 1, 5, 1, 1, 8]
def baseStart_1488984 : Nat := 118140960795 + 1488984 * 2 ^ 59
def prefixEnd_1488984 : Nat := 4983230072969 + 3 ^ 40 * 1488984 * 2
def baseEnd_1488984 : Nat := 84951608761589730772477

theorem tailTrace_1488984 : CollatzResearch.WordTrace tailWord_1488984 prefixEnd_1488984 84951608761589730772477 := by
  unfold tailWord_1488984
  simp only [CollatzResearch.WordTrace]
  refine ⟨27153854018836370533297003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36205138691781827377729337 27153854018836370533297003)
  ·
    refine ⟨40730781028254555799945505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27153854018836370533297003 40730781028254555799945505)
    ·
      refine ⟨30548085771190916849959129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40730781028254555799945505 30548085771190916849959129)
      ·
        refine ⟨22911064328393187637469347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30548085771190916849959129 22911064328393187637469347)
        ·
          refine ⟨34366596492589781456204021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22911064328393187637469347 34366596492589781456204021)
          ·
            refine ⟨3221868421180292011519127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34366596492589781456204021 3221868421180292011519127)
            ·
              refine ⟨4832802631770438017278691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3221868421180292011519127 4832802631770438017278691)
              ·
                refine ⟨7249203947655657025918037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4832802631770438017278691 7249203947655657025918037)
                ·
                  refine ⟨84951608761589730772477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7249203947655657025918037 84951608761589730772477)
                  ·
                    rfl

theorem cell23_1488984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 8].length) (baseStart_1488984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1488984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1488984 prefixEnd_1488984 := by exact prefixLift 1488984
  have htrace : WordTrace (prefixWord ++ tailWord_1488984) baseStart_1488984 baseEnd_1488984 := by
    simpa [prefixWord, tailWord_1488984, baseEnd_1488984] using wordTrace_append hprefix tailTrace_1488984
  have hstable : (prefixWord ++ tailWord_1488984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488984).length < 2 ^ (prefixWord ++ tailWord_1488984).sum := by decide
  have hdescent : baseEnd_1488984 < baseStart_1488984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488988 : List Nat := [2, 2, 4, 1, 1, 3, 2, 1, 3, 4]
def baseStart_1488988 : Nat := 118140960795 + 1488988 * 2 ^ 59
def prefixEnd_1488988 : Nat := 4983230072969 + 3 ^ 40 * 1488988 * 2
def baseEnd_1488988 : Nat := 254855510925641853767425

theorem tailTrace_1488988 : CollatzResearch.WordTrace tailWord_1488988 prefixEnd_1488988 254855510925641853767425 := by
  unfold tailWord_1488988
  simp only [CollatzResearch.WordTrace]
  refine ⟨27153926964829124874869809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36205235953105499833159745 27153926964829124874869809)
  ·
    refine ⟨20365445223621843656152357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27153926964829124874869809 20365445223621843656152357)
    ·
      refine ⟨3818520979429095685528567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20365445223621843656152357 3818520979429095685528567)
      ·
        refine ⟨5727781469143643528292851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3818520979429095685528567 5727781469143643528292851)
        ·
          refine ⟨8591672203715465292439277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5727781469143643528292851 8591672203715465292439277)
          ·
            refine ⟨3221877076393299484664729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8591672203715465292439277 3221877076393299484664729)
            ·
              refine ⟨2416407807294974613498547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3221877076393299484664729 2416407807294974613498547)
              ·
                refine ⟨3624611710942461920247821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2416407807294974613498547 3624611710942461920247821)
                ·
                  refine ⟨1359229391603423220092933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3624611710942461920247821 1359229391603423220092933)
                  ·
                    refine ⟨254855510925641853767425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1359229391603423220092933 254855510925641853767425)
                    ·
                      rfl

theorem cell23_1488988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_1488988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1488988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1488988 prefixEnd_1488988 := by exact prefixLift 1488988
  have htrace : WordTrace (prefixWord ++ tailWord_1488988) baseStart_1488988 baseEnd_1488988 := by
    simpa [prefixWord, tailWord_1488988, baseEnd_1488988] using wordTrace_append hprefix tailTrace_1488988
  have hstable : (prefixWord ++ tailWord_1488988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488988).length < 2 ^ (prefixWord ++ tailWord_1488988).sum := by decide
  have hdescent : baseEnd_1488988 < baseStart_1488988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489001 : List Nat := [1, 2, 1, 1, 1, 5, 5, 1, 6]
def baseStart_1489001 : Nat := 118140960795 + 1489001 * 2 ^ 59
def prefixEnd_1489001 : Nat := 4983230072969 + 3 ^ 40 * 1489001 * 2
def baseEnd_1489001 : Nat := 84952578669492667826635

theorem tailTrace_1489001 : CollatzResearch.WordTrace tailWord_1489001 prefixEnd_1489001 84952578669492667826635 := by
  unfold tailWord_1489001
  simp only [CollatzResearch.WordTrace]
  refine ⟨54308328078611152969962857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36205552052407435313308571 54308328078611152969962857)
  ·
    refine ⟨40731246058958364727472143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54308328078611152969962857 40731246058958364727472143)
    ·
      refine ⟨61096869088437547091208215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40731246058958364727472143 61096869088437547091208215)
      ·
        refine ⟨91645303632656320636812323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61096869088437547091208215 91645303632656320636812323)
        ·
          refine ⟨137467955448984480955218485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91645303632656320636812323 137467955448984480955218485)
          ·
            refine ⟨12887620823342295089551733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 137467955448984480955218485 12887620823342295089551733)
            ·
              refine ⟨1208214452188340164645475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12887620823342295089551733 1208214452188340164645475)
              ·
                refine ⟨1812321678282510246968213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1208214452188340164645475 1812321678282510246968213)
                ·
                  refine ⟨84952578669492667826635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1812321678282510246968213 84952578669492667826635)
                  ·
                    rfl

theorem cell23_1489001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 1, 6].length) (baseStart_1489001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1489001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1489001 prefixEnd_1489001 := by exact prefixLift 1489001
  have htrace : WordTrace (prefixWord ++ tailWord_1489001) baseStart_1489001 baseEnd_1489001 := by
    simpa [prefixWord, tailWord_1489001, baseEnd_1489001] using wordTrace_append hprefix tailTrace_1489001
  have hstable : (prefixWord ++ tailWord_1489001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489001).length < 2 ^ (prefixWord ++ tailWord_1489001).sum := by decide
  have hdescent : baseEnd_1489001 < baseStart_1489001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489031 : List Nat := [1, 1, 4, 2, 1, 1, 4, 3, 1, 5]
def baseStart_1489031 : Nat := 118140960795 + 1489031 * 2 ^ 59
def prefixEnd_1489031 : Nat := 4983230072969 + 3 ^ 40 * 1489031 * 2
def baseEnd_1489031 : Nat := 254862870815022964354859

theorem tailTrace_1489031 : CollatzResearch.WordTrace tailWord_1489031 prefixEnd_1489031 254862870815022964354859 := by
  unfold tailWord_1489031
  simp only [CollatzResearch.WordTrace]
  refine ⟨54309422268502468093554947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36206281512334978729036631 54309422268502468093554947)
  ·
    refine ⟨81464133402753702140332421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54309422268502468093554947 81464133402753702140332421)
    ·
      refine ⟨15274525013016319151312329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81464133402753702140332421 15274525013016319151312329)
      ·
        refine ⟨11455893759762239363484247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15274525013016319151312329 11455893759762239363484247)
        ·
          refine ⟨17183840639643359045226371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11455893759762239363484247 17183840639643359045226371)
          ·
            refine ⟨25775760959465038567839557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17183840639643359045226371 25775760959465038567839557)
            ·
              refine ⟨4832955179899694731469917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25775760959465038567839557 4832955179899694731469917)
              ·
                refine ⟨1812358192462385524301219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4832955179899694731469917 1812358192462385524301219)
                ·
                  refine ⟨2718537288693578286451829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1812358192462385524301219 2718537288693578286451829)
                  ·
                    refine ⟨254862870815022964354859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2718537288693578286451829 254862870815022964354859)
                    ·
                      rfl

theorem cell23_1489031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 3, 1, 5].length) (baseStart_1489031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1489031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1489031 prefixEnd_1489031 := by exact prefixLift 1489031
  have htrace : WordTrace (prefixWord ++ tailWord_1489031) baseStart_1489031 baseEnd_1489031 := by
    simpa [prefixWord, tailWord_1489031, baseEnd_1489031] using wordTrace_append hprefix tailTrace_1489031
  have hstable : (prefixWord ++ tailWord_1489031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489031).length < 2 ^ (prefixWord ++ tailWord_1489031).sum := by decide
  have hdescent : baseEnd_1489031 < baseStart_1489031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489074 : List Nat := [3, 2, 1, 1, 1, 3, 1, 11]
def baseStart_1489074 : Nat := 118140960795 + 1489074 * 2 ^ 59
def prefixEnd_1489074 : Nat := 4983230072969 + 3 ^ 40 * 1489074 * 2
def baseEnd_1489074 : Nat := 28318914522711563882477

theorem tailTrace_1489074 : CollatzResearch.WordTrace tailWord_1489074 prefixEnd_1489074 28318914522711563882477 := by
  unfold tailWord_1489074
  simp only [CollatzResearch.WordTrace]
  refine ⟨13577747651836671609342569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36207327071564457624913517 13577747651836671609342569)
  ·
    refine ⟨10183310738877503707006927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13577747651836671609342569 10183310738877503707006927)
    ·
      refine ⟨15274966108316255560510391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10183310738877503707006927 15274966108316255560510391)
      ·
        refine ⟨22912449162474383340765587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15274966108316255560510391 22912449162474383340765587)
        ·
          refine ⟨34368673743711575011148381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22912449162474383340765587 34368673743711575011148381)
          ·
            refine ⟨12888252653891840629180643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34368673743711575011148381 12888252653891840629180643)
            ·
              refine ⟨19332378980837760943770965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12888252653891840629180643 19332378980837760943770965)
              ·
                refine ⟨28318914522711563882477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 19332378980837760943770965 28318914522711563882477)
                ·
                  rfl

theorem cell23_1489074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 11].length) (baseStart_1489074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1489074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1489074 prefixEnd_1489074 := by exact prefixLift 1489074
  have htrace : WordTrace (prefixWord ++ tailWord_1489074) baseStart_1489074 baseEnd_1489074 := by
    simpa [prefixWord, tailWord_1489074, baseEnd_1489074] using wordTrace_append hprefix tailTrace_1489074
  have hstable : (prefixWord ++ tailWord_1489074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489074).length < 2 ^ (prefixWord ++ tailWord_1489074).sum := by decide
  have hdescent : baseEnd_1489074 < baseStart_1489074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489081 : List Nat := [1, 2, 1, 4, 1, 2, 3, 2, 1, 2, 4]
def baseStart_1489081 : Nat := 118140960795 + 1489081 * 2 ^ 59
def prefixEnd_1489081 : Nat := 4983230072969 + 3 ^ 40 * 1489081 * 2
def baseEnd_1489081 : Nat := 764614286477793697439347

theorem tailTrace_1489081 : CollatzResearch.WordTrace tailWord_1489081 prefixEnd_1489081 764614286477793697439347 := by
  unfold tailWord_1489081
  simp only [CollatzResearch.WordTrace]
  refine ⟨54311245918321326632875097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36207497278880884421916731 54311245918321326632875097)
  ·
    refine ⟨40733434438740994974656323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54311245918321326632875097 40733434438740994974656323)
    ·
      refine ⟨61100151658111492461984485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40733434438740994974656323 61100151658111492461984485)
      ·
        refine ⟨11456278435895904836622091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61100151658111492461984485 11456278435895904836622091)
        ·
          refine ⟨17184417653843857254933137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11456278435895904836622091 17184417653843857254933137)
          ·
            refine ⟨12888313240382892941199853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17184417653843857254933137 12888313240382892941199853)
            ·
              refine ⟨4833117465143584852949945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12888313240382892941199853 4833117465143584852949945)
              ·
                refine ⟨3624838098857688639712459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4833117465143584852949945 3624838098857688639712459)
                ·
                  refine ⟨5437257148286532959568689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3624838098857688639712459 5437257148286532959568689)
                  ·
                    refine ⟨4077942861214899719676517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5437257148286532959568689 4077942861214899719676517)
                    ·
                      refine ⟨764614286477793697439347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4077942861214899719676517 764614286477793697439347)
                      ·
                        rfl

theorem cell23_1489081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_1489081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1489081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1489081 prefixEnd_1489081 := by exact prefixLift 1489081
  have htrace : WordTrace (prefixWord ++ tailWord_1489081) baseStart_1489081 baseEnd_1489081 := by
    simpa [prefixWord, tailWord_1489081, baseEnd_1489081] using wordTrace_append hprefix tailTrace_1489081
  have hstable : (prefixWord ++ tailWord_1489081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489081).length < 2 ^ (prefixWord ++ tailWord_1489081).sum := by decide
  have hdescent : baseEnd_1489081 < baseStart_1489081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489088 : List Nat := [2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 5]
def baseStart_1489088 : Nat := 118140960795 + 1489088 * 2 ^ 59
def prefixEnd_1489088 : Nat := 4983230072969 + 3 ^ 40 * 1489088 * 2
def baseEnd_1489088 : Nat := 764617880842375170051815

theorem tailTrace_1489088 : CollatzResearch.WordTrace tailWord_1489088 prefixEnd_1489088 764617880842375170051815 := by
  unfold tailWord_1489088
  simp only [CollatzResearch.WordTrace]
  refine ⟨27155750614647983414189959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36207667486197311218919945 27155750614647983414189959)
  ·
    refine ⟨40733625921971975121284939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27155750614647983414189959 40733625921971975121284939)
    ·
      refine ⟨61100438882957962681927409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40733625921971975121284939 61100438882957962681927409)
      ·
        refine ⟨45825329162218472011445557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61100438882957962681927409 45825329162218472011445557)
        ·
          refine ⟨4296124608957981751073021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45825329162218472011445557 4296124608957981751073021)
          ·
            refine ⟨1611046728359243156652383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4296124608957981751073021 1611046728359243156652383)
            ·
              refine ⟨2416570092538864734978575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1611046728359243156652383 2416570092538864734978575)
              ·
                refine ⟨3624855138808297102467863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2416570092538864734978575 3624855138808297102467863)
                ·
                  refine ⟨5437282708212445653701795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3624855138808297102467863 5437282708212445653701795)
                  ·
                    refine ⟨8155924062318668480552693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5437282708212445653701795 8155924062318668480552693)
                    ·
                      refine ⟨764617880842375170051815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8155924062318668480552693 764617880842375170051815)
                      ·
                        rfl

theorem cell23_1489088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 5].length) (baseStart_1489088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1489088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1489088 prefixEnd_1489088 := by exact prefixLift 1489088
  have htrace : WordTrace (prefixWord ++ tailWord_1489088) baseStart_1489088 baseEnd_1489088 := by
    simpa [prefixWord, tailWord_1489088, baseEnd_1489088] using wordTrace_append hprefix tailTrace_1489088
  have hstable : (prefixWord ++ tailWord_1489088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489088).length < 2 ^ (prefixWord ++ tailWord_1489088).sum := by decide
  have hdescent : baseEnd_1489088 < baseStart_1489088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489175 : List Nat := [1, 1, 3, 4, 1, 2, 3, 1, 1, 4, 2]
def baseStart_1489175 : Nat := 118140960795 + 1489175 * 2 ^ 59
def prefixEnd_1489175 : Nat := 4983230072969 + 3 ^ 40 * 1489175 * 2
def baseEnd_1489175 : Nat := 764662553659316329663915

theorem tailTrace_1489175 : CollatzResearch.WordTrace tailWord_1489175 prefixEnd_1489175 764662553659316329663915 := by
  unfold tailWord_1489175
  simp only [CollatzResearch.WordTrace]
  refine ⟨54314674379980780686796979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36209782919987187124531319 54314674379980780686796979)
  ·
    refine ⟨81472011569971171030195469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54314674379980780686796979 81472011569971171030195469)
    ·
      refine ⟨30552004338739189136323301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81472011569971171030195469 30552004338739189136323301)
      ·
        refine ⟨5728500813513597963060619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30552004338739189136323301 5728500813513597963060619)
        ·
          refine ⟨8592751220270396944590929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5728500813513597963060619 8592751220270396944590929)
          ·
            refine ⟨6444563415202797708443197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8592751220270396944590929 6444563415202797708443197)
            ·
              refine ⟨2416711280701049140666199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6444563415202797708443197 2416711280701049140666199)
              ·
                refine ⟨3625066921051573710999299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2416711280701049140666199 3625066921051573710999299)
                ·
                  refine ⟨5437600381577360566498949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3625066921051573710999299 5437600381577360566498949)
                  ·
                    refine ⟨1019550071545755106218553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5437600381577360566498949 1019550071545755106218553)
                    ·
                      refine ⟨764662553659316329663915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1019550071545755106218553 764662553659316329663915)
                      ·
                        rfl

theorem cell23_1489175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_1489175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1489175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1489175 prefixEnd_1489175 := by exact prefixLift 1489175
  have htrace : WordTrace (prefixWord ++ tailWord_1489175) baseStart_1489175 baseEnd_1489175 := by
    simpa [prefixWord, tailWord_1489175, baseEnd_1489175] using wordTrace_append hprefix tailTrace_1489175
  have hstable : (prefixWord ++ tailWord_1489175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489175).length < 2 ^ (prefixWord ++ tailWord_1489175).sum := by decide
  have hdescent : baseEnd_1489175 < baseStart_1489175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489215 : List Nat := [1, 1, 2, 2, 4, 1, 5, 2, 5]
def baseStart_1489215 : Nat := 118140960795 + 1489215 * 2 ^ 59
def prefixEnd_1489215 : Nat := 4983230072969 + 3 ^ 40 * 1489215 * 2
def baseEnd_1489215 : Nat := 84964788098388463684859

theorem tailTrace_1489215 : CollatzResearch.WordTrace tailWord_1489215 prefixEnd_1489215 84964788098388463684859 := by
  unfold tailWord_1489215
  simp only [CollatzResearch.WordTrace]
  refine ⟨54316133299835867518253099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36210755533223911678835399 54316133299835867518253099)
  ·
    refine ⟨81474199949753801277379649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54316133299835867518253099 81474199949753801277379649)
    ·
      refine ⟨61105649962315350958034737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81474199949753801277379649 61105649962315350958034737)
      ·
        refine ⟨45829237471736513218526053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61105649962315350958034737 45829237471736513218526053)
        ·
          refine ⟨8592982025950596228473635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45829237471736513218526053 8592982025950596228473635)
          ·
            refine ⟨12889473038925894342710453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8592982025950596228473635 12889473038925894342710453)
            ·
              refine ⟨1208388097399302594629105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12889473038925894342710453 1208388097399302594629105)
              ·
                refine ⟨906291073049476945971829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1208388097399302594629105 906291073049476945971829)
                ·
                  refine ⟨84964788098388463684859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 906291073049476945971829 84964788098388463684859)
                  ·
                    rfl

theorem cell23_1489215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 2, 5].length) (baseStart_1489215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1489215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1489215 prefixEnd_1489215 := by exact prefixLift 1489215
  have htrace : WordTrace (prefixWord ++ tailWord_1489215) baseStart_1489215 baseEnd_1489215 := by
    simpa [prefixWord, tailWord_1489215, baseEnd_1489215] using wordTrace_append hprefix tailTrace_1489215
  have hstable : (prefixWord ++ tailWord_1489215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489215).length < 2 ^ (prefixWord ++ tailWord_1489215).sum := by decide
  have hdescent : baseEnd_1489215 < baseStart_1489215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489231 : List Nat := [1, 1, 2, 1, 1, 2, 1, 6, 1, 3, 4]
def baseStart_1489231 : Nat := 118140960795 + 1489231 * 2 ^ 59
def prefixEnd_1489231 : Nat := 4983230072969 + 3 ^ 40 * 1489231 * 2
def baseEnd_1489231 : Nat := 764691308575968110563657

theorem tailTrace_1489231 : CollatzResearch.WordTrace tailWord_1489231 prefixEnd_1489231 764691308575968110563657 := by
  unfold tailWord_1489231
  simp only [CollatzResearch.WordTrace]
  refine ⟨54316716867777902250835547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36211144578518601500557031 54316716867777902250835547)
  ·
    refine ⟨81475075301666853376253321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54316716867777902250835547 81475075301666853376253321)
    ·
      refine ⟨61106306476250140032189991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81475075301666853376253321 61106306476250140032189991)
      ·
        refine ⟨91659459714375210048284987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61106306476250140032189991 91659459714375210048284987)
        ·
          refine ⟨137489189571562815072427481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91659459714375210048284987 137489189571562815072427481)
          ·
            refine ⟨103116892178672111304320611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137489189571562815072427481 103116892178672111304320611)
            ·
              refine ⟨154675338268008166956480917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103116892178672111304320611 154675338268008166956480917)
              ·
                refine ⟨7250406481312882826085043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 154675338268008166956480917 7250406481312882826085043)
                ·
                  refine ⟨10875609721969324239127565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7250406481312882826085043 10875609721969324239127565)
                  ·
                    refine ⟨4078353645738496589672837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10875609721969324239127565 4078353645738496589672837)
                    ·
                      refine ⟨764691308575968110563657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4078353645738496589672837 764691308575968110563657)
                      ·
                        rfl

theorem cell23_1489231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 3, 4].length) (baseStart_1489231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1489231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1489231 prefixEnd_1489231 := by exact prefixLift 1489231
  have htrace : WordTrace (prefixWord ++ tailWord_1489231) baseStart_1489231 baseEnd_1489231 := by
    simpa [prefixWord, tailWord_1489231, baseEnd_1489231] using wordTrace_append hprefix tailTrace_1489231
  have hstable : (prefixWord ++ tailWord_1489231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489231).length < 2 ^ (prefixWord ++ tailWord_1489231).sum := by decide
  have hdescent : baseEnd_1489231 < baseStart_1489231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489288 : List Nat := [2, 1, 3, 3, 1, 1, 1, 5, 6]
def baseStart_1489288 : Nat := 118140960795 + 1489288 * 2 ^ 59
def prefixEnd_1489288 : Nat := 4983230072969 + 3 ^ 40 * 1489288 * 2
def baseEnd_1489288 : Nat := 84968952997030487505655

theorem tailTrace_1489288 : CollatzResearch.WordTrace tailWord_1489288 prefixEnd_1489288 84968952997030487505655 := by
  unfold tailWord_1489288
  simp only [CollatzResearch.WordTrace]
  refine ⟨27159397914285700492830259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36212530552380933990440345 27159397914285700492830259)
  ·
    refine ⟨40739096871428550739245389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27159397914285700492830259 40739096871428550739245389)
    ·
      refine ⟨15277161326785706527217021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40739096871428550739245389 15277161326785706527217021)
      ·
        refine ⟨5728935497544639947706383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15277161326785706527217021 5728935497544639947706383)
        ·
          refine ⟨8593403246316959921559575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5728935497544639947706383 8593403246316959921559575)
          ·
            refine ⟨12890104869475439882339363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8593403246316959921559575 12890104869475439882339363)
            ·
              refine ⟨19335157304213159823509045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12890104869475439882339363 19335157304213159823509045)
              ·
                refine ⟨1812670997269983733453973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19335157304213159823509045 1812670997269983733453973)
                ·
                  refine ⟨84968952997030487505655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1812670997269983733453973 84968952997030487505655)
                  ·
                    rfl

theorem cell23_1489288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 5, 6].length) (baseStart_1489288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1489288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1489288 prefixEnd_1489288 := by exact prefixLift 1489288
  have htrace : WordTrace (prefixWord ++ tailWord_1489288) baseStart_1489288 baseEnd_1489288 := by
    simpa [prefixWord, tailWord_1489288, baseEnd_1489288] using wordTrace_append hprefix tailTrace_1489288
  have hstable : (prefixWord ++ tailWord_1489288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489288).length < 2 ^ (prefixWord ++ tailWord_1489288).sum := by decide
  have hdescent : baseEnd_1489288 < baseStart_1489288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489309 : List Nat := [1, 4, 2, 1, 4, 1, 2, 3, 1, 4]
def baseStart_1489309 : Nat := 118140960795 + 1489309 * 2 ^ 59
def prefixEnd_1489309 : Nat := 4983230072969 + 3 ^ 40 * 1489309 * 2
def baseEnd_1489309 : Nat := 254910453355672935129433

theorem tailTrace_1489309 : CollatzResearch.WordTrace tailWord_1489309 prefixEnd_1489309 254910453355672935129433 := by
  unfold tailWord_1489309
  simp only [CollatzResearch.WordTrace]
  refine ⟨54319561761495321572174981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36213041174330214381449987 54319561761495321572174981)
  ·
    refine ⟨10184917830280372794782809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54319561761495321572174981 10184917830280372794782809)
    ·
      refine ⟨7638688372710279596087107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10184917830280372794782809 7638688372710279596087107)
      ·
        refine ⟨11458032559065419394130661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7638688372710279596087107 11458032559065419394130661)
        ·
          refine ⟨2148381104824766136399499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11458032559065419394130661 2148381104824766136399499)
          ·
            refine ⟨3222571657237149204599249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2148381104824766136399499 3222571657237149204599249)
            ·
              refine ⟨2416928742927861903449437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3222571657237149204599249 2416928742927861903449437)
              ·
                refine ⟨906348278597948213793539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2416928742927861903449437 906348278597948213793539)
                ·
                  refine ⟨1359522417896922320690309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 906348278597948213793539 1359522417896922320690309)
                  ·
                    refine ⟨254910453355672935129433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1359522417896922320690309 254910453355672935129433)
                    ·
                      rfl

theorem cell23_1489309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 3, 1, 4].length) (baseStart_1489309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1489309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1489309 prefixEnd_1489309 := by exact prefixLift 1489309
  have htrace : WordTrace (prefixWord ++ tailWord_1489309) baseStart_1489309 baseEnd_1489309 := by
    simpa [prefixWord, tailWord_1489309, baseEnd_1489309] using wordTrace_append hprefix tailTrace_1489309
  have hstable : (prefixWord ++ tailWord_1489309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489309).length < 2 ^ (prefixWord ++ tailWord_1489309).sum := by decide
  have hdescent : baseEnd_1489309 < baseStart_1489309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489331 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 2, 10]
def baseStart_1489331 : Nat := 118140960795 + 1489331 * 2 ^ 59
def prefixEnd_1489331 : Nat := 4983230072969 + 3 ^ 40 * 1489331 * 2
def baseEnd_1489331 : Nat := 254914218880472573104399

theorem tailTrace_1489331 : CollatzResearch.WordTrace tailWord_1489331 prefixEnd_1489331 254914218880472573104399 := by
  unfold tailWord_1489331
  simp only [CollatzResearch.WordTrace]
  refine ⟨54320364167415619329475847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36213576111610412886317231 54320364167415619329475847)
  ·
    refine ⟨81480546251123428994213771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54320364167415619329475847 81480546251123428994213771)
    ·
      refine ⟨122220819376685143491320657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81480546251123428994213771 122220819376685143491320657)
      ·
        refine ⟨91665614532513857618490493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122220819376685143491320657 91665614532513857618490493)
        ·
          refine ⟨34374605449692696606933935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91665614532513857618490493 34374605449692696606933935)
          ·
            refine ⟨51561908174539044910400903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34374605449692696606933935 51561908174539044910400903)
            ·
              refine ⟨77342862261808567365601355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51561908174539044910400903 77342862261808567365601355)
              ·
                refine ⟨116014293392712851048402033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77342862261808567365601355 116014293392712851048402033)
                ·
                  refine ⟨87010720044534638286301525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116014293392712851048402033 87010720044534638286301525)
                  ·
                    refine ⟨254914218880472573104399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 87010720044534638286301525 254914218880472573104399)
                    ·
                      rfl

theorem cell23_1489331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 10].length) (baseStart_1489331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1489331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1489331 prefixEnd_1489331 := by exact prefixLift 1489331
  have htrace : WordTrace (prefixWord ++ tailWord_1489331) baseStart_1489331 baseEnd_1489331 := by
    simpa [prefixWord, tailWord_1489331, baseEnd_1489331] using wordTrace_append hprefix tailTrace_1489331
  have hstable : (prefixWord ++ tailWord_1489331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489331).length < 2 ^ (prefixWord ++ tailWord_1489331).sum := by decide
  have hdescent : baseEnd_1489331 < baseStart_1489331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489338 : List Nat := [3, 1, 1, 1, 2, 1, 1, 3, 5, 1, 4]
def baseStart_1489338 : Nat := 118140960795 + 1489338 * 2 ^ 59
def prefixEnd_1489338 : Nat := 4983230072969 + 3 ^ 40 * 1489338 * 2
def baseEnd_1489338 : Nat := 764746251005999191925665

theorem tailTrace_1489338 : CollatzResearch.WordTrace tailWord_1489338 prefixEnd_1489338 764746251005999191925665 := by
  unfold tailWord_1489338
  simp only [CollatzResearch.WordTrace]
  refine ⟨13580154869597564881245167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36213746318926839683320445 13580154869597564881245167)
  ·
    refine ⟨20370232304396347321867751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13580154869597564881245167 20370232304396347321867751)
    ·
      refine ⟨30555348456594520982801627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20370232304396347321867751 30555348456594520982801627)
      ·
        refine ⟨45833022684891781474202441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30555348456594520982801627 45833022684891781474202441)
        ·
          refine ⟨34374767013668836105651831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45833022684891781474202441 34374767013668836105651831)
          ·
            refine ⟨51562150520503254158477747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34374767013668836105651831 51562150520503254158477747)
            ·
              refine ⟨77343225780754881237716621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51562150520503254158477747 77343225780754881237716621)
              ·
                refine ⟨29003709667783080464143733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77343225780754881237716621 29003709667783080464143733)
                ·
                  refine ⟨2719097781354663793513475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29003709667783080464143733 2719097781354663793513475)
                  ·
                    refine ⟨4078646672031995690270213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2719097781354663793513475 4078646672031995690270213)
                    ·
                      refine ⟨764746251005999191925665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4078646672031995690270213 764746251005999191925665)
                      ·
                        rfl

theorem cell23_1489338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 5, 1, 4].length) (baseStart_1489338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1489338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1489338 prefixEnd_1489338 := by exact prefixLift 1489338
  have htrace : WordTrace (prefixWord ++ tailWord_1489338) baseStart_1489338 baseEnd_1489338 := by
    simpa [prefixWord, tailWord_1489338, baseEnd_1489338] using wordTrace_append hprefix tailTrace_1489338
  have hstable : (prefixWord ++ tailWord_1489338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489338).length < 2 ^ (prefixWord ++ tailWord_1489338).sum := by decide
  have hdescent : baseEnd_1489338 < baseStart_1489338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489358 : List Nat := [4, 1, 1, 1, 2, 1, 1, 1, 5, 1, 5]
def baseStart_1489358 : Nat := 118140960795 + 1489358 * 2 ^ 59
def prefixEnd_1489358 : Nat := 4983230072969 + 3 ^ 40 * 1489358 * 2
def baseEnd_1489358 : Nat := 764756520619089113675573

theorem tailTrace_1489358 : CollatzResearch.WordTrace tailWord_1489358 prefixEnd_1489358 764756520619089113675573 := by
  unfold tailWord_1489358
  simp only [CollatzResearch.WordTrace]
  refine ⟨6790168617289725367588591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36214232625545201960472485 6790168617289725367588591)
  ·
    refine ⟨10185252925934588051382887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6790168617289725367588591 10185252925934588051382887)
    ·
      refine ⟨15277879388901882077074331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10185252925934588051382887 15277879388901882077074331)
      ·
        refine ⟨22916819083352823115611497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15277879388901882077074331 22916819083352823115611497)
        ·
          refine ⟨17187614312514617336708623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22916819083352823115611497 17187614312514617336708623)
          ·
            refine ⟨25781421468771926005062935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17187614312514617336708623 25781421468771926005062935)
            ·
              refine ⟨38672132203157889007594403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25781421468771926005062935 38672132203157889007594403)
              ·
                refine ⟨58008198304736833511391605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38672132203157889007594403 58008198304736833511391605)
                ·
                  refine ⟨5438268591069078141692963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58008198304736833511391605 5438268591069078141692963)
                  ·
                    refine ⟨8157402886603617212539445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5438268591069078141692963 8157402886603617212539445)
                    ·
                      refine ⟨764756520619089113675573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8157402886603617212539445 764756520619089113675573)
                      ·
                        rfl

theorem cell23_1489358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_1489358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1489358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1489358 prefixEnd_1489358 := by exact prefixLift 1489358
  have htrace : WordTrace (prefixWord ++ tailWord_1489358) baseStart_1489358 baseEnd_1489358 := by
    simpa [prefixWord, tailWord_1489358, baseEnd_1489358] using wordTrace_append hprefix tailTrace_1489358
  have hstable : (prefixWord ++ tailWord_1489358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489358).length < 2 ^ (prefixWord ++ tailWord_1489358).sum := by decide
  have hdescent : baseEnd_1489358 < baseStart_1489358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489365 : List Nat := [1, 3, 2, 3, 1, 2, 1, 2, 4, 4]
def baseStart_1489365 : Nat := 118140960795 + 1489365 * 2 ^ 59
def prefixEnd_1489365 : Nat := 4983230072969 + 3 ^ 40 * 1489365 * 2
def baseEnd_1489365 : Nat := 254920038327890195429347

theorem tailTrace_1489365 : CollatzResearch.WordTrace tailWord_1489365 prefixEnd_1489365 254920038327890195429347 := by
  unfold tailWord_1489365
  simp only [CollatzResearch.WordTrace]
  refine ⟨54321604249292443136213549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36214402832861628757475699 54321604249292443136213549)
  ·
    refine ⟨20370601593484666176080081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54321604249292443136213549 20370601593484666176080081)
    ·
      refine ⟨15277951195113499632060061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20370601593484666176080081 15277951195113499632060061)
      ·
        refine ⟨5729231698167562362022523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15277951195113499632060061 5729231698167562362022523)
        ·
          refine ⟨8593847547251343543033785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5729231698167562362022523 8593847547251343543033785)
          ·
            refine ⟨6445385660438507657275339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8593847547251343543033785 6445385660438507657275339)
            ·
              refine ⟨9668078490657761485913009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6445385660438507657275339 9668078490657761485913009)
              ·
                refine ⟨7251058867993321114434757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9668078490657761485913009 7251058867993321114434757)
                ·
                  refine ⟨1359573537748747708956517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7251058867993321114434757 1359573537748747708956517)
                  ·
                    refine ⟨254920038327890195429347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1359573537748747708956517 254920038327890195429347)
                    ·
                      rfl

theorem cell23_1489365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 4, 4].length) (baseStart_1489365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1489365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1489365 prefixEnd_1489365 := by exact prefixLift 1489365
  have htrace : WordTrace (prefixWord ++ tailWord_1489365) baseStart_1489365 baseEnd_1489365 := by
    simpa [prefixWord, tailWord_1489365, baseEnd_1489365] using wordTrace_append hprefix tailTrace_1489365
  have hstable : (prefixWord ++ tailWord_1489365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489365).length < 2 ^ (prefixWord ++ tailWord_1489365).sum := by decide
  have hdescent : baseEnd_1489365 < baseStart_1489365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489368 : List Nat := [2, 1, 2, 2, 2, 1, 1, 3, 3, 2, 4]
def baseStart_1489368 : Nat := 118140960795 + 1489368 * 2 ^ 59
def prefixEnd_1489368 : Nat := 4983230072969 + 3 ^ 40 * 1489368 * 2
def baseEnd_1489368 : Nat := 764761655425634074550527

theorem tailTrace_1489368 : CollatzResearch.WordTrace tailWord_1489368 prefixEnd_1489368 764761655425634074550527 := by
  unfold tailWord_1489368
  simp only [CollatzResearch.WordTrace]
  refine ⟨27160856834140787324286379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36214475778854383099048505 27160856834140787324286379)
  ·
    refine ⟨40741285251211180986429569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27160856834140787324286379 40741285251211180986429569)
    ·
      refine ⟨30555963938408385739822177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40741285251211180986429569 30555963938408385739822177)
      ·
        refine ⟨22916972953806289304866633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30555963938408385739822177 22916972953806289304866633)
        ·
          refine ⟨17187729715354716978649975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22916972953806289304866633 17187729715354716978649975)
          ·
            refine ⟨25781594573032075467974963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17187729715354716978649975 25781594573032075467974963)
            ·
              refine ⟨38672391859548113201962445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25781594573032075467974963 38672391859548113201962445)
              ·
                refine ⟨14502146947330542450735917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38672391859548113201962445 14502146947330542450735917)
                ·
                  refine ⟨5438305105248953419025969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14502146947330542450735917 5438305105248953419025969)
                  ·
                    refine ⟨4078728828936715064269477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5438305105248953419025969 4078728828936715064269477)
                    ·
                      refine ⟨764761655425634074550527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4078728828936715064269477 764761655425634074550527)
                      ·
                        rfl

theorem cell23_1489368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_1489368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1489368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1489368 prefixEnd_1489368 := by exact prefixLift 1489368
  have htrace : WordTrace (prefixWord ++ tailWord_1489368) baseStart_1489368 baseEnd_1489368 := by
    simpa [prefixWord, tailWord_1489368, baseEnd_1489368] using wordTrace_append hprefix tailTrace_1489368
  have hstable : (prefixWord ++ tailWord_1489368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489368).length < 2 ^ (prefixWord ++ tailWord_1489368).sum := by decide
  have hdescent : baseEnd_1489368 < baseStart_1489368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489375 : List Nat := [1, 1, 2, 3, 3, 3, 2, 1, 1, 1, 5]
def baseStart_1489375 : Nat := 118140960795 + 1489375 * 2 ^ 59
def prefixEnd_1489375 : Nat := 4983230072969 + 3 ^ 40 * 1489375 * 2
def baseEnd_1489375 : Nat := 764765249790215547162995

theorem tailTrace_1489375 : CollatzResearch.WordTrace tailWord_1489375 prefixEnd_1489375 764765249790215547162995 := by
  unfold tailWord_1489375
  simp only [CollatzResearch.WordTrace]
  refine ⟨54321968979256214844077579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36214645986170809896051719 54321968979256214844077579)
  ·
    refine ⟨81482953468884322266116369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54321968979256214844077579 81482953468884322266116369)
    ·
      refine ⟨61112215101663241699587277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81482953468884322266116369 61112215101663241699587277)
      ·
        refine ⟨22917080663123715637345229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61112215101663241699587277 22917080663123715637345229)
        ·
          refine ⟨8593905248671393364004461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22917080663123715637345229 8593905248671393364004461)
          ·
            refine ⟨3222714468251772511501673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8593905248671393364004461 3222714468251772511501673)
            ·
              refine ⟨2417035851188829383626255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3222714468251772511501673 2417035851188829383626255)
              ·
                refine ⟨3625553776783244075439383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2417035851188829383626255 3625553776783244075439383)
                ·
                  refine ⟨5438330665174866113159075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3625553776783244075439383 5438330665174866113159075)
                  ·
                    refine ⟨8157495997762299169738613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5438330665174866113159075 8157495997762299169738613)
                    ·
                      refine ⟨764765249790215547162995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8157495997762299169738613 764765249790215547162995)
                      ·
                        rfl

theorem cell23_1489375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 1, 1, 1, 5].length) (baseStart_1489375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1489375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1489375 prefixEnd_1489375 := by exact prefixLift 1489375
  have htrace : WordTrace (prefixWord ++ tailWord_1489375) baseStart_1489375 baseEnd_1489375 := by
    simpa [prefixWord, tailWord_1489375, baseEnd_1489375] using wordTrace_append hprefix tailTrace_1489375
  have hstable : (prefixWord ++ tailWord_1489375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489375).length < 2 ^ (prefixWord ++ tailWord_1489375).sum := by decide
  have hdescent : baseEnd_1489375 < baseStart_1489375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489405 : List Nat := [1, 4, 1, 1, 1, 3, 2, 3, 1, 3, 3]
def baseStart_1489405 : Nat := 118140960795 + 1489405 * 2 ^ 59
def prefixEnd_1489405 : Nat := 4983230072969 + 3 ^ 40 * 1489405 * 2
def baseEnd_1489405 : Nat := 764780654209850429787857

theorem tailTrace_1489405 : CollatzResearch.WordTrace tailWord_1489405 prefixEnd_1489405 764780654209850429787857 := by
  unfold tailWord_1489405
  simp only [CollatzResearch.WordTrace]
  refine ⟨54323063169147529967669669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36215375446098353311779779 54323063169147529967669669)
  ·
    refine ⟨10185574344215161868938063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54323063169147529967669669 10185574344215161868938063)
    ·
      refine ⟨15278361516322742803407095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10185574344215161868938063 15278361516322742803407095)
      ·
        refine ⟨22917542274484114205110643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15278361516322742803407095 22917542274484114205110643)
        ·
          refine ⟨34376313411726171307665965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22917542274484114205110643 34376313411726171307665965)
          ·
            refine ⟨12891117529397314240374737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34376313411726171307665965 12891117529397314240374737)
            ·
              refine ⟨9668338147047985680281053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12891117529397314240374737 9668338147047985680281053)
              ·
                refine ⟨3625626805142994630105395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9668338147047985680281053 3625626805142994630105395)
                ·
                  refine ⟨5438440207714491945158093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3625626805142994630105395 5438440207714491945158093)
                  ·
                    refine ⟨2039415077892934479434285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5438440207714491945158093 2039415077892934479434285)
                    ·
                      refine ⟨764780654209850429787857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2039415077892934479434285 764780654209850429787857)
                      ·
                        rfl

theorem cell23_1489405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3, 1, 3, 3].length) (baseStart_1489405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1489405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1489405 prefixEnd_1489405 := by exact prefixLift 1489405
  have htrace : WordTrace (prefixWord ++ tailWord_1489405) baseStart_1489405 baseEnd_1489405 := by
    simpa [prefixWord, tailWord_1489405, baseEnd_1489405] using wordTrace_append hprefix tailTrace_1489405
  have hstable : (prefixWord ++ tailWord_1489405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489405).length < 2 ^ (prefixWord ++ tailWord_1489405).sum := by decide
  have hdescent : baseEnd_1489405 < baseStart_1489405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489409 : List Nat := [1, 2, 4, 1, 3, 3, 1, 2, 1, 2, 3]
def baseStart_1489409 : Nat := 118140960795 + 1489409 * 2 ^ 59
def prefixEnd_1489409 : Nat := 4983230072969 + 3 ^ 40 * 1489409 * 2
def baseEnd_1489409 : Nat := 764782708132468414137839

theorem tailTrace_1489409 : CollatzResearch.WordTrace tailWord_1489409 prefixEnd_1489409 764782708132468414137839 := by
  unfold tailWord_1489409
  simp only [CollatzResearch.WordTrace]
  refine ⟨54323209061133038650815281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36215472707422025767210187 54323209061133038650815281)
  ·
    refine ⟨40742406795849778988111461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54323209061133038650815281 40742406795849778988111461)
    ·
      refine ⟨7639201274221833560270899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40742406795849778988111461 7639201274221833560270899)
      ·
        refine ⟨11458801911332750340406349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7639201274221833560270899 11458801911332750340406349)
        ·
          refine ⟨4297050716749781377652381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11458801911332750340406349 4297050716749781377652381)
          ·
            refine ⟨1611394018781168016619643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4297050716749781377652381 1611394018781168016619643)
            ·
              refine ⟨2417091028171752024929465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1611394018781168016619643 2417091028171752024929465)
              ·
                refine ⟨1812818271128814018697099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2417091028171752024929465 1812818271128814018697099)
                ·
                  refine ⟨2719227406693221028045649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1812818271128814018697099 2719227406693221028045649)
                  ·
                    refine ⟨2039420555019915771034237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2719227406693221028045649 2039420555019915771034237)
                    ·
                      refine ⟨764782708132468414137839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2039420555019915771034237 764782708132468414137839)
                      ·
                        rfl

theorem cell23_1489409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_1489409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1489409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1489409 prefixEnd_1489409 := by exact prefixLift 1489409
  have htrace : WordTrace (prefixWord ++ tailWord_1489409) baseStart_1489409 baseEnd_1489409 := by
    simpa [prefixWord, tailWord_1489409, baseEnd_1489409] using wordTrace_append hprefix tailTrace_1489409
  have hstable : (prefixWord ++ tailWord_1489409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489409).length < 2 ^ (prefixWord ++ tailWord_1489409).sum := by decide
  have hdescent : baseEnd_1489409 < baseStart_1489409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489422 : List Nat := [4, 1, 1, 2, 3, 2, 1, 2, 1, 3, 3]
def baseStart_1489422 : Nat := 118140960795 + 1489422 * 2 ^ 59
def prefixEnd_1489422 : Nat := 4983230072969 + 3 ^ 40 * 1489422 * 2
def baseEnd_1489422 : Nat := 764789383380976863275279

theorem tailTrace_1489422 : CollatzResearch.WordTrace tailWord_1489422 prefixEnd_1489422 764789383380976863275279 := by
  unfold tailWord_1489422
  simp only [CollatzResearch.WordTrace]
  refine ⟨6790460401260742733879815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36215788806723961247359013 6790460401260742733879815)
  ·
    refine ⟨10185690601891114100819723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6790460401260742733879815 10185690601891114100819723)
    ·
      refine ⟨15278535902836671151229585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10185690601891114100819723 15278535902836671151229585)
      ·
        refine ⟨11458901927127503363422189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15278535902836671151229585 11458901927127503363422189)
        ·
          refine ⟨4297088222672813761283321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11458901927127503363422189 4297088222672813761283321)
          ·
            refine ⟨3222816167004610320962491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4297088222672813761283321 3222816167004610320962491)
            ·
              refine ⟨4834224250506915481443737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3222816167004610320962491 4834224250506915481443737)
              ·
                refine ⟨3625668187880186611082803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4834224250506915481443737 3625668187880186611082803)
                ·
                  refine ⟨5438502281820279916624205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3625668187880186611082803 5438502281820279916624205)
                  ·
                    refine ⟨2039438355682604968734077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5438502281820279916624205 2039438355682604968734077)
                    ·
                      refine ⟨764789383380976863275279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2039438355682604968734077 764789383380976863275279)
                      ·
                        rfl

theorem cell23_1489422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_1489422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1489422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1489422 prefixEnd_1489422 := by exact prefixLift 1489422
  have htrace : WordTrace (prefixWord ++ tailWord_1489422) baseStart_1489422 baseEnd_1489422 := by
    simpa [prefixWord, tailWord_1489422, baseEnd_1489422] using wordTrace_append hprefix tailTrace_1489422
  have hstable : (prefixWord ++ tailWord_1489422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489422).length < 2 ^ (prefixWord ++ tailWord_1489422).sum := by decide
  have hdescent : baseEnd_1489422 < baseStart_1489422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489440 : List Nat := [2, 1, 1, 6, 2, 2, 2, 2, 1, 2, 2]
def baseStart_1489440 : Nat := 118140960795 + 1489440 * 2 ^ 59
def prefixEnd_1489440 : Nat := 4983230072969 + 3 ^ 40 * 1489440 * 2
def baseEnd_1489440 : Nat := 764798626032757792850197

theorem tailTrace_1489440 : CollatzResearch.WordTrace tailWord_1489440 prefixEnd_1489440 764798626032757792850197 := by
  unfold tailWord_1489440
  simp only [CollatzResearch.WordTrace]
  refine ⟨27162169862010365472596887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36216226482680487296795849 27162169862010365472596887)
  ·
    refine ⟨40743254793015548208895331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27162169862010365472596887 40743254793015548208895331)
    ·
      refine ⟨61114882189523322313342997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40743254793015548208895331 61114882189523322313342997)
      ·
        refine ⟨2864760102633905733437953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 61114882189523322313342997 2864760102633905733437953)
        ·
          refine ⟨2148570076975429300078465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2864760102633905733437953 2148570076975429300078465)
          ·
            refine ⟨1611427557731571975058849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2148570076975429300078465 1611427557731571975058849)
            ·
              refine ⟨1208570668298678981294137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1611427557731571975058849 1208570668298678981294137)
              ·
                refine ⟨906428001224009235970603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1208570668298678981294137 906428001224009235970603)
                ·
                  refine ⟨1359642001836013853955905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 906428001224009235970603 1359642001836013853955905)
                  ·
                    refine ⟨1019731501377010390466929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1359642001836013853955905 1019731501377010390466929)
                    ·
                      refine ⟨764798626032757792850197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1019731501377010390466929 764798626032757792850197)
                      ·
                        rfl

theorem cell23_1489440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_1489440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1489440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1489440 prefixEnd_1489440 := by exact prefixLift 1489440
  have htrace : WordTrace (prefixWord ++ tailWord_1489440) baseStart_1489440 baseEnd_1489440 := by
    simpa [prefixWord, tailWord_1489440, baseEnd_1489440] using wordTrace_append hprefix tailTrace_1489440
  have hstable : (prefixWord ++ tailWord_1489440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489440).length < 2 ^ (prefixWord ++ tailWord_1489440).sum := by decide
  have hdescent : baseEnd_1489440 < baseStart_1489440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489465 : List Nat := [1, 2, 1, 5, 1, 1, 1, 2, 2, 4, 3]
def baseStart_1489465 : Nat := 118140960795 + 1489465 * 2 ^ 59
def prefixEnd_1489465 : Nat := 4983230072969 + 3 ^ 40 * 1489465 * 2
def baseEnd_1489465 : Nat := 764811463049120195037581

theorem tailTrace_1489465 : CollatzResearch.WordTrace tailWord_1489465 prefixEnd_1489465 764811463049120195037581 := by
  unfold tailWord_1489465
  simp only [CollatzResearch.WordTrace]
  refine ⟨54325251548930160214853849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36216834365953440143235899 54325251548930160214853849)
  ·
    refine ⟨40743938661697620161140387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54325251548930160214853849 40743938661697620161140387)
    ·
      refine ⟨61115907992546430241710581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40743938661697620161140387 61115907992546430241710581)
      ·
        refine ⟨5729616374301227835160367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61115907992546430241710581 5729616374301227835160367)
        ·
          refine ⟨8594424561451841752740551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5729616374301227835160367 8594424561451841752740551)
          ·
            refine ⟨12891636842177762629110827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8594424561451841752740551 12891636842177762629110827)
            ·
              refine ⟨19337455263266643943666241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12891636842177762629110827 19337455263266643943666241)
              ·
                refine ⟨14503091447449982957749681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19337455263266643943666241 14503091447449982957749681)
                ·
                  refine ⟨10877318585587487218312261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14503091447449982957749681 10877318585587487218312261)
                  ·
                    refine ⟨2039497234797653853433549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10877318585587487218312261 2039497234797653853433549)
                    ·
                      refine ⟨764811463049120195037581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2039497234797653853433549 764811463049120195037581)
                      ·
                        rfl

theorem cell23_1489465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_1489465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1489465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1489465 prefixEnd_1489465 := by exact prefixLift 1489465
  have htrace : WordTrace (prefixWord ++ tailWord_1489465) baseStart_1489465 baseEnd_1489465 := by
    simpa [prefixWord, tailWord_1489465, baseEnd_1489465] using wordTrace_append hprefix tailTrace_1489465
  have hstable : (prefixWord ++ tailWord_1489465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489465).length < 2 ^ (prefixWord ++ tailWord_1489465).sum := by decide
  have hdescent : baseEnd_1489465 < baseStart_1489465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489495 : List Nat := [1, 1, 3, 2, 2, 2, 1, 1, 4, 3, 3]
def baseStart_1489495 : Nat := 118140960795 + 1489495 * 2 ^ 59
def prefixEnd_1489495 : Nat := 4983230072969 + 3 ^ 40 * 1489495 * 2
def baseEnd_1489495 : Nat := 764826867468755077662443

theorem tailTrace_1489495 : CollatzResearch.WordTrace tailWord_1489495 prefixEnd_1489495 764826867468755077662443 := by
  unfold tailWord_1489495
  simp only [CollatzResearch.WordTrace]
  refine ⟨54326345738821475338445939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36217563825880983558963959 54326345738821475338445939)
  ·
    refine ⟨81489518608232213007668909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54326345738821475338445939 81489518608232213007668909)
    ·
      refine ⟨30558569478087079877875841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81489518608232213007668909 30558569478087079877875841)
      ·
        refine ⟨22918927108565309908406881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30558569478087079877875841 22918927108565309908406881)
        ·
          refine ⟨17189195331423982431305161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22918927108565309908406881 17189195331423982431305161)
          ·
            refine ⟨12891896498567986823478871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17189195331423982431305161 12891896498567986823478871)
            ·
              refine ⟨19337844747851980235218307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12891896498567986823478871 19337844747851980235218307)
              ·
                refine ⟨29006767121777970352827461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19337844747851980235218307 29006767121777970352827461)
                ·
                  refine ⟨5438768835333369441155149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29006767121777970352827461 5438768835333369441155149)
                  ·
                    refine ⟨2039538313250013540433181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5438768835333369441155149 2039538313250013540433181)
                    ·
                      refine ⟨764826867468755077662443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2039538313250013540433181 764826867468755077662443)
                      ·
                        rfl

theorem cell23_1489495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4, 3, 3].length) (baseStart_1489495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1489495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1489495 prefixEnd_1489495 := by exact prefixLift 1489495
  have htrace : WordTrace (prefixWord ++ tailWord_1489495) baseStart_1489495 baseEnd_1489495 := by
    simpa [prefixWord, tailWord_1489495, baseEnd_1489495] using wordTrace_append hprefix tailTrace_1489495
  have hstable : (prefixWord ++ tailWord_1489495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489495).length < 2 ^ (prefixWord ++ tailWord_1489495).sum := by decide
  have hdescent : baseEnd_1489495 < baseStart_1489495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489565 : List Nat := [1, 4, 2, 1, 1, 1, 2, 2, 2, 1, 6]
def baseStart_1489565 : Nat := 118140960795 + 1489565 * 2 ^ 59
def prefixEnd_1489565 : Nat := 4983230072969 + 3 ^ 40 * 1489565 * 2
def baseEnd_1489565 : Nat := 764862811114569803787121

theorem tailTrace_1489565 : CollatzResearch.WordTrace tailWord_1489565 prefixEnd_1489565 764862811114569803787121 := by
  unfold tailWord_1489565
  simp only [CollatzResearch.WordTrace]
  refine ⟨54328898848567877293494149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36219265899045251528996099 54328898848567877293494149)
  ·
    refine ⟨10186668534106476992530153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54328898848567877293494149 10186668534106476992530153)
    ·
      refine ⟨7640001400579857744397615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10186668534106476992530153 7640001400579857744397615)
      ·
        refine ⟨11460002100869786616596423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7640001400579857744397615 11460002100869786616596423)
        ·
          refine ⟨17190003151304679924894635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11460002100869786616596423 17190003151304679924894635)
          ·
            refine ⟨25785004726957019887341953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17190003151304679924894635 25785004726957019887341953)
            ·
              refine ⟨19338753545217764915506465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25785004726957019887341953 19338753545217764915506465)
              ·
                refine ⟨14504065158913323686629849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19338753545217764915506465 14504065158913323686629849)
                ·
                  refine ⟨10878048869184992764972387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14504065158913323686629849 10878048869184992764972387)
                  ·
                    refine ⟨16317073303777489147458581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10878048869184992764972387 16317073303777489147458581)
                    ·
                      refine ⟨764862811114569803787121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16317073303777489147458581 764862811114569803787121)
                      ·
                        rfl

theorem cell23_1489565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_1489565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1489565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1489565 prefixEnd_1489565 := by exact prefixLift 1489565
  have htrace : WordTrace (prefixWord ++ tailWord_1489565) baseStart_1489565 baseEnd_1489565 := by
    simpa [prefixWord, tailWord_1489565, baseEnd_1489565] using wordTrace_append hprefix tailTrace_1489565
  have hstable : (prefixWord ++ tailWord_1489565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489565).length < 2 ^ (prefixWord ++ tailWord_1489565).sum := by decide
  have hdescent : baseEnd_1489565 < baseStart_1489565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489572 : List Nat := [2, 3, 1, 2, 2, 1, 1, 2, 4, 2, 3]
def baseStart_1489572 : Nat := 118140960795 + 1489572 * 2 ^ 59
def prefixEnd_1489572 : Nat := 4983230072969 + 3 ^ 40 * 1489572 * 2
def baseEnd_1489572 : Nat := 764866405479151276399589

theorem tailTrace_1489572 : CollatzResearch.WordTrace tailWord_1489572 prefixEnd_1489572 764866405479151276399589 := by
  unfold tailWord_1489572
  simp only [CollatzResearch.WordTrace]
  refine ⟨27164577079771258744499485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36219436106361678325999313 27164577079771258744499485)
  ·
    refine ⟨10186716404914222029187307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27164577079771258744499485 10186716404914222029187307)
    ·
      refine ⟨15280074607371333043780961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10186716404914222029187307 15280074607371333043780961)
      ·
        refine ⟨11460055955528499782835721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15280074607371333043780961 11460055955528499782835721)
        ·
          refine ⟨8595041966646374837126791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11460055955528499782835721 8595041966646374837126791)
          ·
            refine ⟨12892562949969562255690187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8595041966646374837126791 12892562949969562255690187)
            ·
              refine ⟨19338844424954343383535281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12892562949969562255690187 19338844424954343383535281)
              ·
                refine ⟨14504133318715757537651461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19338844424954343383535281 14504133318715757537651461)
                ·
                  refine ⟨2719524997259204538309649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14504133318715757537651461 2719524997259204538309649)
                  ·
                    refine ⟨2039643747944403403732237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2719524997259204538309649 2039643747944403403732237)
                    ·
                      refine ⟨764866405479151276399589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2039643747944403403732237 764866405479151276399589)
                      ·
                        rfl

theorem cell23_1489572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_1489572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1489572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1489572 prefixEnd_1489572 := by exact prefixLift 1489572
  have htrace : WordTrace (prefixWord ++ tailWord_1489572) baseStart_1489572 baseEnd_1489572 := by
    simpa [prefixWord, tailWord_1489572, baseEnd_1489572] using wordTrace_append hprefix tailTrace_1489572
  have hstable : (prefixWord ++ tailWord_1489572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489572).length < 2 ^ (prefixWord ++ tailWord_1489572).sum := by decide
  have hdescent : baseEnd_1489572 < baseStart_1489572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489589 : List Nat := [1, 3, 3, 3, 1, 1, 1, 3, 2, 2, 3]
def baseStart_1489589 : Nat := 118140960795 + 1489589 * 2 ^ 59
def prefixEnd_1489589 : Nat := 4983230072969 + 3 ^ 40 * 1489589 * 2
def baseEnd_1489589 : Nat := 764875134650277709887011

theorem tailTrace_1489589 : CollatzResearch.WordTrace tailWord_1489589 prefixEnd_1489589 764875134650277709887011 := by
  unfold tailWord_1489589
  simp only [CollatzResearch.WordTrace]
  refine ⟨54329774200480929392367821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36219849466987286261578547 54329774200480929392367821)
  ·
    refine ⟨20373665325180348522137933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54329774200480929392367821 20373665325180348522137933)
    ·
      refine ⟨7640124496942630695801725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20373665325180348522137933 7640124496942630695801725)
      ·
        refine ⟨2865046686353486510925647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7640124496942630695801725 2865046686353486510925647)
        ·
          refine ⟨4297570029530229766388471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2865046686353486510925647 4297570029530229766388471)
          ·
            refine ⟨6446355044295344649582707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4297570029530229766388471 6446355044295344649582707)
            ·
              refine ⟨9669532566443016974374061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6446355044295344649582707 9669532566443016974374061)
              ·
                refine ⟨3626074712416131365390273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9669532566443016974374061 3626074712416131365390273)
                ·
                  refine ⟨2719556034312098524042705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3626074712416131365390273 2719556034312098524042705)
                  ·
                    refine ⟨2039667025734073893032029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2719556034312098524042705 2039667025734073893032029)
                    ·
                      refine ⟨764875134650277709887011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2039667025734073893032029 764875134650277709887011)
                      ·
                        rfl

theorem cell23_1489589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_1489589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1489589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1489589 prefixEnd_1489589 := by exact prefixLift 1489589
  have htrace : WordTrace (prefixWord ++ tailWord_1489589) baseStart_1489589 baseEnd_1489589 := by
    simpa [prefixWord, tailWord_1489589, baseEnd_1489589] using wordTrace_append hprefix tailTrace_1489589
  have hstable : (prefixWord ++ tailWord_1489589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489589).length < 2 ^ (prefixWord ++ tailWord_1489589).sum := by decide
  have hdescent : baseEnd_1489589 < baseStart_1489589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489605 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 7, 5]
def baseStart_1489605 : Nat := 118140960795 + 1489605 * 2 ^ 59
def prefixEnd_1489605 : Nat := 4983230072969 + 3 ^ 40 * 1489605 * 2
def baseEnd_1489605 : Nat := 254961116780249882428979

theorem tailTrace_1489605 : CollatzResearch.WordTrace tailWord_1489605 prefixEnd_1489605 254961116780249882428979 := by
  unfold tailWord_1489605
  simp only [CollatzResearch.WordTrace]
  refine ⟨54330357768422964124950269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36220238512281976083300179 54330357768422964124950269)
  ·
    refine ⟨20373884163158611546856351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54330357768422964124950269 20373884163158611546856351)
    ·
      refine ⟨30560826244737917320284527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20373884163158611546856351 30560826244737917320284527)
      ·
        refine ⟨45841239367106875980426791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30560826244737917320284527 45841239367106875980426791)
        ·
          refine ⟨68761859050660313970640187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45841239367106875980426791 68761859050660313970640187)
          ·
            refine ⟨103142788575990470955960281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68761859050660313970640187 103142788575990470955960281)
            ·
              refine ⟨77357091431992853216970211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103142788575990470955960281 77357091431992853216970211)
              ·
                refine ⟨116035637147989279825455317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77357091431992853216970211 116035637147989279825455317)
                ·
                  refine ⟨2719585245655998745909109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 116035637147989279825455317 2719585245655998745909109)
                  ·
                    refine ⟨254961116780249882428979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2719585245655998745909109 254961116780249882428979)
                    ·
                      rfl

theorem cell23_1489605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 7, 5].length) (baseStart_1489605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1489605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1489605 prefixEnd_1489605 := by exact prefixLift 1489605
  have htrace : WordTrace (prefixWord ++ tailWord_1489605) baseStart_1489605 baseEnd_1489605 := by
    simpa [prefixWord, tailWord_1489605, baseEnd_1489605] using wordTrace_append hprefix tailTrace_1489605
  have hstable : (prefixWord ++ tailWord_1489605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489605).length < 2 ^ (prefixWord ++ tailWord_1489605).sum := by decide
  have hdescent : baseEnd_1489605 < baseStart_1489605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489646 : List Nat := [4, 1, 2, 1, 1, 3, 3, 1, 2, 3, 2]
def baseStart_1489646 : Nat := 118140960795 + 1489646 * 2 ^ 59
def prefixEnd_1489646 : Nat := 4983230072969 + 3 ^ 40 * 1489646 * 2
def baseEnd_1489646 : Nat := 764904403047583986874249

theorem tailTrace_1489646 : CollatzResearch.WordTrace tailWord_1489646 prefixEnd_1489646 764904403047583986874249 := by
  unfold tailWord_1489646
  simp only [CollatzResearch.WordTrace]
  refine ⟨6791481645159303515899099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36221235440849618751461861 6791481645159303515899099)
  ·
    refine ⟨10187222467738955273848649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6791481645159303515899099 10187222467738955273848649)
    ·
      refine ⟨7640416850804216455386487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10187222467738955273848649 7640416850804216455386487)
      ·
        refine ⟨11460625276206324683079731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7640416850804216455386487 11460625276206324683079731)
        ·
          refine ⟨17190937914309487024619597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11460625276206324683079731 17190937914309487024619597)
          ·
            refine ⟨6446601717866057634232349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17190937914309487024619597 6446601717866057634232349)
            ·
              refine ⟨2417475644199771612837131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6446601717866057634232349 2417475644199771612837131)
              ·
                refine ⟨3626213466299657419255697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2417475644199771612837131 3626213466299657419255697)
                ·
                  refine ⟨2719660099724743064441773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3626213466299657419255697 2719660099724743064441773)
                  ·
                    refine ⟨1019872537396778649165665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2719660099724743064441773 1019872537396778649165665)
                    ·
                      refine ⟨764904403047583986874249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1019872537396778649165665 764904403047583986874249)
                      ·
                        rfl

theorem cell23_1489646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 1, 2, 3, 2].length) (baseStart_1489646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1489646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1489646 prefixEnd_1489646 := by exact prefixLift 1489646
  have htrace : WordTrace (prefixWord ++ tailWord_1489646) baseStart_1489646 baseEnd_1489646 := by
    simpa [prefixWord, tailWord_1489646, baseEnd_1489646] using wordTrace_append hprefix tailTrace_1489646
  have hstable : (prefixWord ++ tailWord_1489646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489646).length < 2 ^ (prefixWord ++ tailWord_1489646).sum := by decide
  have hdescent : baseEnd_1489646 < baseStart_1489646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489655 : List Nat := [1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 6]
def baseStart_1489655 : Nat := 118140960795 + 1489655 * 2 ^ 59
def prefixEnd_1489655 : Nat := 4983230072969 + 3 ^ 40 * 1489655 * 2
def baseEnd_1489655 : Nat := 764909024373474451661707

theorem tailTrace_1489655 : CollatzResearch.WordTrace tailWord_1489655 prefixEnd_1489655 764909024373474451661707 := by
  unfold tailWord_1489655
  simp only [CollatzResearch.WordTrace]
  refine ⟨54332181418241822664270419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36221454278827881776180279 54332181418241822664270419)
  ·
    refine ⟨81498272127362733996405629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54332181418241822664270419 81498272127362733996405629)
    ·
      refine ⟨30561852047761025248652111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81498272127362733996405629 30561852047761025248652111)
      ·
        refine ⟨45842778071641537872978167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30561852047761025248652111 45842778071641537872978167)
        ·
          refine ⟨68764167107462306809467251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45842778071641537872978167 68764167107462306809467251)
          ·
            refine ⟨103146250661193460214200877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68764167107462306809467251 103146250661193460214200877)
            ·
              refine ⟨38679843997947547580325329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103146250661193460214200877 38679843997947547580325329)
              ·
                refine ⟨29009882998460660685243997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38679843997947547580325329 29009882998460660685243997)
                ·
                  refine ⟨10878706124422747756966499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29009882998460660685243997 10878706124422747756966499)
                  ·
                    refine ⟨16318059186634121635449749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10878706124422747756966499 16318059186634121635449749)
                    ·
                      refine ⟨764909024373474451661707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16318059186634121635449749 764909024373474451661707)
                      ·
                        rfl

theorem cell23_1489655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 6].length) (baseStart_1489655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1489655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1489655 prefixEnd_1489655 := by exact prefixLift 1489655
  have htrace : WordTrace (prefixWord ++ tailWord_1489655) baseStart_1489655 baseEnd_1489655 := by
    simpa [prefixWord, tailWord_1489655, baseEnd_1489655] using wordTrace_append hprefix tailTrace_1489655
  have hstable : (prefixWord ++ tailWord_1489655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489655).length < 2 ^ (prefixWord ++ tailWord_1489655).sum := by decide
  have hdescent : baseEnd_1489655 < baseStart_1489655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489675 : List Nat := [1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 7]
def baseStart_1489675 : Nat := 118140960795 + 1489675 * 2 ^ 59
def prefixEnd_1489675 : Nat := 4983230072969 + 3 ^ 40 * 1489675 * 2
def baseEnd_1489675 : Nat := 764919293986564373411615

theorem tailTrace_1489675 : CollatzResearch.WordTrace tailWord_1489675 prefixEnd_1489675 764919293986564373411615 := by
  unfold tailWord_1489675
  simp only [CollatzResearch.WordTrace]
  refine ⟨54332910878169366079998479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36221940585446244053332319 54332910878169366079998479)
  ·
    refine ⟨81499366317254049119997719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54332910878169366079998479 81499366317254049119997719)
    ·
      refine ⟨122249049475881073679996579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81499366317254049119997719 122249049475881073679996579)
      ·
        refine ⟨183373574213821610519994869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122249049475881073679996579 183373574213821610519994869)
        ·
          refine ⟨17191272582545775986249519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 183373574213821610519994869 17191272582545775986249519)
          ·
            refine ⟨25786908873818663979374279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17191272582545775986249519 25786908873818663979374279)
            ·
              refine ⟨38680363310727995969061419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25786908873818663979374279 38680363310727995969061419)
              ·
                refine ⟨58020544966091993953592129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38680363310727995969061419 58020544966091993953592129)
                ·
                  refine ⟨43515408724568995465194097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58020544966091993953592129 43515408724568995465194097)
                  ·
                    refine ⟨32636556543426746598895573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43515408724568995465194097 32636556543426746598895573)
                    ·
                      refine ⟨764919293986564373411615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 32636556543426746598895573 764919293986564373411615)
                      ·
                        rfl

theorem cell23_1489675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 7].length) (baseStart_1489675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1489675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1489675 prefixEnd_1489675 := by exact prefixLift 1489675
  have htrace : WordTrace (prefixWord ++ tailWord_1489675) baseStart_1489675 baseEnd_1489675 := by
    simpa [prefixWord, tailWord_1489675, baseEnd_1489675] using wordTrace_append hprefix tailTrace_1489675
  have hstable : (prefixWord ++ tailWord_1489675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489675).length < 2 ^ (prefixWord ++ tailWord_1489675).sum := by decide
  have hdescent : baseEnd_1489675 < baseStart_1489675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489693 : List Nat := [1, 4, 2, 4, 1, 1, 2, 2, 1, 1, 4]
def baseStart_1489693 : Nat := 118140960795 + 1489693 * 2 ^ 59
def prefixEnd_1489693 : Nat := 4983230072969 + 3 ^ 40 * 1489693 * 2
def baseEnd_1489693 : Nat := 764928536638345302986533

theorem tailTrace_1489693 : CollatzResearch.WordTrace tailWord_1489693 prefixEnd_1489693 764928536638345302986533 := by
  unfold tailWord_1489693
  simp only [CollatzResearch.WordTrace]
  refine ⟨54333567392104155154153733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36222378261402770102769155 54333567392104155154153733)
  ·
    refine ⟨10187543886019529091403825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54333567392104155154153733 10187543886019529091403825)
    ·
      refine ⟨7640657914514646818552869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10187543886019529091403825 7640657914514646818552869)
      ·
        refine ⟨1432623358971496278478663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7640657914514646818552869 1432623358971496278478663)
        ·
          refine ⟨2148935038457244417717995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1432623358971496278478663 2148935038457244417717995)
          ·
            refine ⟨3223402557685866626576993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2148935038457244417717995 3223402557685866626576993)
            ·
              refine ⟨2417551918264399969932745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3223402557685866626576993 2417551918264399969932745)
              ·
                refine ⟨1813163938698299977449559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2417551918264399969932745 1813163938698299977449559)
                ·
                  refine ⟨2719745908047449966174339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1813163938698299977449559 2719745908047449966174339)
                  ·
                    refine ⟨4079618862071174949261509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2719745908047449966174339 4079618862071174949261509)
                    ·
                      refine ⟨764928536638345302986533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4079618862071174949261509 764928536638345302986533)
                      ·
                        rfl

theorem cell23_1489693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_1489693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1489693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1489693 prefixEnd_1489693 := by exact prefixLift 1489693
  have htrace : WordTrace (prefixWord ++ tailWord_1489693) baseStart_1489693 baseEnd_1489693 := by
    simpa [prefixWord, tailWord_1489693, baseEnd_1489693] using wordTrace_append hprefix tailTrace_1489693
  have hstable : (prefixWord ++ tailWord_1489693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489693).length < 2 ^ (prefixWord ++ tailWord_1489693).sum := by decide
  have hdescent : baseEnd_1489693 < baseStart_1489693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489696 : List Nat := [2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 3]
def baseStart_1489696 : Nat := 118140960795 + 1489696 * 2 ^ 59
def prefixEnd_1489696 : Nat := 4983230072969 + 3 ^ 40 * 1489696 * 2
def baseEnd_1489696 : Nat := 764930077080308791249019

theorem tailTrace_1489696 : CollatzResearch.WordTrace tailWord_1489696 prefixEnd_1489696 764930077080308791249019 := by
  unfold tailWord_1489696
  simp only [CollatzResearch.WordTrace]
  refine ⟨27166838405546643333256471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36222451207395524444341961 27166838405546643333256471)
  ·
    refine ⟨40750257608319964999884707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27166838405546643333256471 40750257608319964999884707)
    ·
      refine ⟨61125386412479947499827061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40750257608319964999884707 61125386412479947499827061)
      ·
        refine ⟨5730504976169995078108787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61125386412479947499827061 5730504976169995078108787)
        ·
          refine ⟨8595757464254992617163181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5730504976169995078108787 8595757464254992617163181)
          ·
            refine ⟨3223409049095622231436193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8595757464254992617163181 3223409049095622231436193)
            ·
              refine ⟨2417556786821716673577145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3223409049095622231436193 2417556786821716673577145)
              ·
                refine ⟨1813167590116287505182859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2417556786821716673577145 1813167590116287505182859)
                ·
                  refine ⟨2719751385174431257774289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1813167590116287505182859 2719751385174431257774289)
                  ·
                    refine ⟨2039813538880823443330717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2719751385174431257774289 2039813538880823443330717)
                    ·
                      refine ⟨764930077080308791249019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2039813538880823443330717 764930077080308791249019)
                      ·
                        rfl

theorem cell23_1489696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_1489696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1489696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1489696 prefixEnd_1489696 := by exact prefixLift 1489696
  have htrace : WordTrace (prefixWord ++ tailWord_1489696) baseStart_1489696 baseEnd_1489696 := by
    simpa [prefixWord, tailWord_1489696, baseEnd_1489696] using wordTrace_append hprefix tailTrace_1489696
  have hstable : (prefixWord ++ tailWord_1489696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489696).length < 2 ^ (prefixWord ++ tailWord_1489696).sum := by decide
  have hdescent : baseEnd_1489696 < baseStart_1489696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489716 : List Nat := [2, 5, 1, 1, 4, 1, 9]
def baseStart_1489716 : Nat := 118140960795 + 1489716 * 2 ^ 59
def prefixEnd_1489716 : Nat := 4983230072969 + 3 ^ 40 * 1489716 * 2
def baseEnd_1489716 : Nat := 9443707983869119913567

theorem tailTrace_1489716 : CollatzResearch.WordTrace tailWord_1489716 prefixEnd_1489716 9443707983869119913567 := by
  unfold tailWord_1489716
  simp only [CollatzResearch.WordTrace]
  refine ⟨27167203135510415041120501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36222937514013886721494001 27167203135510415041120501)
  ·
    refine ⟨2546925293954101410105047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27167203135510415041120501 2546925293954101410105047)
    ·
      refine ⟨3820387940931152115157571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2546925293954101410105047 3820387940931152115157571)
      ·
        refine ⟨5730581911396728172736357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3820387940931152115157571 5730581911396728172736357)
        ·
          refine ⟨1074484108386886532388067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5730581911396728172736357 1074484108386886532388067)
          ·
            refine ⟨1611726162580329798582101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1074484108386886532388067 1611726162580329798582101)
            ·
              refine ⟨9443707983869119913567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1611726162580329798582101 9443707983869119913567)
              ·
                rfl

theorem cell23_1489716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 9].length) (baseStart_1489716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1489716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1489716 prefixEnd_1489716 := by exact prefixLift 1489716
  have htrace : WordTrace (prefixWord ++ tailWord_1489716) baseStart_1489716 baseEnd_1489716 := by
    simpa [prefixWord, tailWord_1489716, baseEnd_1489716] using wordTrace_append hprefix tailTrace_1489716
  have hstable : (prefixWord ++ tailWord_1489716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489716).length < 2 ^ (prefixWord ++ tailWord_1489716).sum := by decide
  have hdescent : baseEnd_1489716 < baseStart_1489716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489742 : List Nat := [4, 1, 1, 1, 1, 1, 1, 5, 2, 6]
def baseStart_1489742 : Nat := 118140960795 + 1489742 * 2 ^ 59
def prefixEnd_1489742 : Nat := 4983230072969 + 3 ^ 40 * 1489742 * 2
def baseEnd_1489742 : Nat := 254984565730138537091269

theorem tailTrace_1489742 : CollatzResearch.WordTrace tailWord_1489742 prefixEnd_1489742 254984565730138537091269 := by
  unfold tailWord_1489742
  simp only [CollatzResearch.WordTrace]
  refine ⟨6791919321115829565335935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36223569712617757681791653 6791919321115829565335935)
  ·
    refine ⟨10187878981673744348003903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6791919321115829565335935 10187878981673744348003903)
    ·
      refine ⟨15281818472510616522005855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10187878981673744348003903 15281818472510616522005855)
      ·
        refine ⟨22922727708765924783008783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15281818472510616522005855 22922727708765924783008783)
        ·
          refine ⟨34384091563148887174513175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22922727708765924783008783 34384091563148887174513175)
          ·
            refine ⟨51576137344723330761769763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34384091563148887174513175 51576137344723330761769763)
            ·
              refine ⟨77364206017084996142654645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51576137344723330761769763 77364206017084996142654645)
              ·
                refine ⟨7252894314101718388373873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77364206017084996142654645 7252894314101718388373873)
                ·
                  refine ⟨5439670735576288791280405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7252894314101718388373873 5439670735576288791280405)
                  ·
                    refine ⟨254984565730138537091269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5439670735576288791280405 254984565730138537091269)
                    ·
                      rfl

theorem cell23_1489742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 2, 6].length) (baseStart_1489742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1489742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1489742 prefixEnd_1489742 := by exact prefixLift 1489742
  have htrace : WordTrace (prefixWord ++ tailWord_1489742) baseStart_1489742 baseEnd_1489742 := by
    simpa [prefixWord, tailWord_1489742, baseEnd_1489742] using wordTrace_append hprefix tailTrace_1489742
  have hstable : (prefixWord ++ tailWord_1489742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489742).length < 2 ^ (prefixWord ++ tailWord_1489742).sum := by decide
  have hdescent : baseEnd_1489742 < baseStart_1489742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489753 : List Nat := [1, 2, 1, 2, 2, 6, 1, 2, 1, 3, 2]
def baseStart_1489753 : Nat := 118140960795 + 1489753 * 2 ^ 59
def prefixEnd_1489753 : Nat := 4983230072969 + 3 ^ 40 * 1489753 * 2
def baseEnd_1489753 : Nat := 764959345477615068236257

theorem tailTrace_1489753 : CollatzResearch.WordTrace tailWord_1489753 prefixEnd_1489753 764959345477615068236257 := by
  unfold tailWord_1489753
  simp only [CollatzResearch.WordTrace]
  refine ⟨54335755771886785401337913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36223837181257856934225275 54335755771886785401337913)
  ·
    refine ⟨40751816828915089051003435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54335755771886785401337913 40751816828915089051003435)
    ·
      refine ⟨61127725243372633576505153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40751816828915089051003435 61127725243372633576505153)
      ·
        refine ⟨45845793932529475182378865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61127725243372633576505153 45845793932529475182378865)
        ·
          refine ⟨34384345449397106386784149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45845793932529475182378865 34384345449397106386784149)
          ·
            refine ⟨1611766192940489361880507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 34384345449397106386784149 1611766192940489361880507)
            ·
              refine ⟨2417649289410734042820761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1611766192940489361880507 2417649289410734042820761)
              ·
                refine ⟨1813236967058050532115571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2417649289410734042820761 1813236967058050532115571)
                ·
                  refine ⟨2719855450587075798173357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1813236967058050532115571 2719855450587075798173357)
                  ·
                    refine ⟨1019945793970153424315009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2719855450587075798173357 1019945793970153424315009)
                    ·
                      refine ⟨764959345477615068236257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1019945793970153424315009 764959345477615068236257)
                      ·
                        rfl

theorem cell23_1489753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 2, 1, 3, 2].length) (baseStart_1489753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1489753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1489753 prefixEnd_1489753 := by exact prefixLift 1489753
  have htrace : WordTrace (prefixWord ++ tailWord_1489753) baseStart_1489753 baseEnd_1489753 := by
    simpa [prefixWord, tailWord_1489753, baseEnd_1489753] using wordTrace_append hprefix tailTrace_1489753
  have hstable : (prefixWord ++ tailWord_1489753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489753).length < 2 ^ (prefixWord ++ tailWord_1489753).sum := by decide
  have hdescent : baseEnd_1489753 < baseStart_1489753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489799 : List Nat := [1, 1, 4, 2, 3, 1, 1, 1, 1, 5, 3]
def baseStart_1489799 : Nat := 118140960795 + 1489799 * 2 ^ 59
def prefixEnd_1489799 : Nat := 4983230072969 + 3 ^ 40 * 1489799 * 2
def baseEnd_1489799 : Nat := 764982965587721888261045

theorem tailTrace_1489799 : CollatzResearch.WordTrace tailWord_1489799 prefixEnd_1489799 764982965587721888261045 := by
  unfold tailWord_1489799
  simp only [CollatzResearch.WordTrace]
  refine ⟨54337433529720135257512451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36224955686480090171674967 54337433529720135257512451)
  ·
    refine ⟨81506150294580202886268677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54337433529720135257512451 81506150294580202886268677)
    ·
      refine ⟨15282403180233788041175377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81506150294580202886268677 15282403180233788041175377)
      ·
        refine ⟨11461802385175341030881533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15282403180233788041175377 11461802385175341030881533)
        ·
          refine ⟨4298175894440752886580575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11461802385175341030881533 4298175894440752886580575)
          ·
            refine ⟨6447263841661129329870863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4298175894440752886580575 6447263841661129329870863)
            ·
              refine ⟨9670895762491693994806295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6447263841661129329870863 9670895762491693994806295)
              ·
                refine ⟨14506343643737540992209443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9670895762491693994806295 14506343643737540992209443)
                ·
                  refine ⟨21759515465606311488314165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14506343643737540992209443 21759515465606311488314165)
                  ·
                    refine ⟨2039954574900591702029453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21759515465606311488314165 2039954574900591702029453)
                    ·
                      refine ⟨764982965587721888261045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2039954574900591702029453 764982965587721888261045)
                      ·
                        rfl

theorem cell23_1489799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_1489799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1489799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1489799 prefixEnd_1489799 := by exact prefixLift 1489799
  have htrace : WordTrace (prefixWord ++ tailWord_1489799) baseStart_1489799 baseEnd_1489799 := by
    simpa [prefixWord, tailWord_1489799, baseEnd_1489799] using wordTrace_append hprefix tailTrace_1489799
  have hstable : (prefixWord ++ tailWord_1489799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489799).length < 2 ^ (prefixWord ++ tailWord_1489799).sum := by decide
  have hdescent : baseEnd_1489799 < baseStart_1489799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489809 : List Nat := [1, 2, 2, 1, 1, 1, 3, 1, 4, 5, 2]
def baseStart_1489809 : Nat := 118140960795 + 1489809 * 2 ^ 59
def prefixEnd_1489809 : Nat := 4983230072969 + 3 ^ 40 * 1489809 * 2
def baseEnd_1489809 : Nat := 764988100394266849135999

theorem tailTrace_1489809 : CollatzResearch.WordTrace tailWord_1489809 prefixEnd_1489809 764988100394266849135999 := by
  unfold tailWord_1489809
  simp only [CollatzResearch.WordTrace]
  refine ⟨54337798259683906965376481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36225198839789271310250987 54337798259683906965376481)
  ·
    refine ⟨40753348694762930224032361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54337798259683906965376481 40753348694762930224032361)
    ·
      refine ⟨30565011521072197668024271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40753348694762930224032361 30565011521072197668024271)
      ·
        refine ⟨45847517281608296502036407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30565011521072197668024271 45847517281608296502036407)
        ·
          refine ⟨68771275922412444753054611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45847517281608296502036407 68771275922412444753054611)
          ·
            refine ⟨103156913883618667129581917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68771275922412444753054611 103156913883618667129581917)
            ·
              refine ⟨38683842706357000173593219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103156913883618667129581917 38683842706357000173593219)
              ·
                refine ⟨58025764059535500260389829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38683842706357000173593219 58025764059535500260389829)
                ·
                  refine ⟨10879830761162906298823093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58025764059535500260389829 10879830761162906298823093)
                  ·
                    refine ⟨1019984133859022465514665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10879830761162906298823093 1019984133859022465514665)
                    ·
                      refine ⟨764988100394266849135999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1019984133859022465514665 764988100394266849135999)
                      ·
                        rfl

theorem cell23_1489809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 5, 2].length) (baseStart_1489809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1489809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1489809 prefixEnd_1489809 := by exact prefixLift 1489809
  have htrace : WordTrace (prefixWord ++ tailWord_1489809) baseStart_1489809 baseEnd_1489809 := by
    simpa [prefixWord, tailWord_1489809, baseEnd_1489809] using wordTrace_append hprefix tailTrace_1489809
  have hstable : (prefixWord ++ tailWord_1489809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489809).length < 2 ^ (prefixWord ++ tailWord_1489809).sum := by decide
  have hdescent : baseEnd_1489809 < baseStart_1489809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489856 : List Nat := [2, 1, 1, 2, 3, 3, 2, 1, 2, 4, 2]
def baseStart_1489856 : Nat := 118140960795 + 1489856 * 2 ^ 59
def prefixEnd_1489856 : Nat := 4983230072969 + 3 ^ 40 * 1489856 * 2
def baseEnd_1489856 : Nat := 765012233985028165248283

theorem tailTrace_1489856 : CollatzResearch.WordTrace tailWord_1489856 prefixEnd_1489856 765012233985028165248283 := by
  unfold tailWord_1489856
  simp only [CollatzResearch.WordTrace]
  refine ⟨27169756245256816996168711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36226341660342422661558281 27169756245256816996168711)
  ·
    refine ⟨40754634367885225494253067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27169756245256816996168711 40754634367885225494253067)
    ·
      refine ⟨61131951551827838241379601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40754634367885225494253067 61131951551827838241379601)
      ·
        refine ⟨45848963663870878681034701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61131951551827838241379601 45848963663870878681034701)
        ·
          refine ⟨17193361373951579505388013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45848963663870878681034701 17193361373951579505388013)
          ·
            refine ⟨6447510515231842314520505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17193361373951579505388013 6447510515231842314520505)
            ·
              refine ⟨4835632886423881735890379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6447510515231842314520505 4835632886423881735890379)
              ·
                refine ⟨7253449329635822603835569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4835632886423881735890379 7253449329635822603835569)
                ·
                  refine ⟨5440086997226866952876677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7253449329635822603835569 5440086997226866952876677)
                  ·
                    refine ⟨1020016311980037553664377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5440086997226866952876677 1020016311980037553664377)
                    ·
                      refine ⟨765012233985028165248283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1020016311980037553664377 765012233985028165248283)
                      ·
                        rfl

theorem cell23_1489856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 2, 4, 2].length) (baseStart_1489856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1489856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1489856 prefixEnd_1489856 := by exact prefixLift 1489856
  have htrace : WordTrace (prefixWord ++ tailWord_1489856) baseStart_1489856 baseEnd_1489856 := by
    simpa [prefixWord, tailWord_1489856, baseEnd_1489856] using wordTrace_append hprefix tailTrace_1489856
  have hstable : (prefixWord ++ tailWord_1489856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489856).length < 2 ^ (prefixWord ++ tailWord_1489856).sum := by decide
  have hdescent : baseEnd_1489856 < baseStart_1489856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489859 : List Nat := [1, 1, 1, 3, 1, 1, 2, 4, 4, 2, 3]
def baseStart_1489859 : Nat := 118140960795 + 1489859 * 2 ^ 59
def prefixEnd_1489859 : Nat := 4983230072969 + 3 ^ 40 * 1489859 * 2
def baseEnd_1489859 : Nat := 765013774426991653510769

theorem tailTrace_1489859 : CollatzResearch.WordTrace tailWord_1489859 prefixEnd_1489859 765013774426991653510769 := by
  unfold tailWord_1489859
  simp only [CollatzResearch.WordTrace]
  refine ⟨54339621909502765504696631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36226414606335177003131087 54339621909502765504696631)
  ·
    refine ⟨81509432864254148257044947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54339621909502765504696631 81509432864254148257044947)
    ·
      refine ⟨122264149296381222385567421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81509432864254148257044947 122264149296381222385567421)
      ·
        refine ⟨45849055986142958394587783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122264149296381222385567421 45849055986142958394587783)
        ·
          refine ⟨68773583979214437591881675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45849055986142958394587783 68773583979214437591881675)
          ·
            refine ⟨103160375968821656387822513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68773583979214437591881675 103160375968821656387822513)
            ·
              refine ⟨77370281976616242290866885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103160375968821656387822513 77370281976616242290866885)
              ·
                refine ⟨14506927870615545429537541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77370281976616242290866885 14506927870615545429537541)
                ·
                  refine ⟨2720048975740414768038289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14506927870615545429537541 2720048975740414768038289)
                  ·
                    refine ⟨2040036731805311076028717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2720048975740414768038289 2040036731805311076028717)
                    ·
                      refine ⟨765013774426991653510769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2040036731805311076028717 765013774426991653510769)
                      ·
                        rfl

theorem cell23_1489859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 4, 2, 3].length) (baseStart_1489859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1489859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1489859 prefixEnd_1489859 := by exact prefixLift 1489859
  have htrace : WordTrace (prefixWord ++ tailWord_1489859) baseStart_1489859 baseEnd_1489859 := by
    simpa [prefixWord, tailWord_1489859, baseEnd_1489859] using wordTrace_append hprefix tailTrace_1489859
  have hstable : (prefixWord ++ tailWord_1489859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489859).length < 2 ^ (prefixWord ++ tailWord_1489859).sum := by decide
  have hdescent : baseEnd_1489859 < baseStart_1489859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489876 : List Nat := [2, 4, 1, 2, 1, 2, 2, 1, 1, 4, 3]
def baseStart_1489876 : Nat := 118140960795 + 1489876 * 2 ^ 59
def prefixEnd_1489876 : Nat := 4983230072969 + 3 ^ 40 * 1489876 * 2
def baseEnd_1489876 : Nat := 765022503598118086998191

theorem tailTrace_1489876 : CollatzResearch.WordTrace tailWord_1489876 prefixEnd_1489876 765022503598118086998191 := by
  unfold tailWord_1489876
  simp only [CollatzResearch.WordTrace]
  refine ⟨27170120975220588704032741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36226827966960784938710321 27170120975220588704032741)
  ·
    refine ⟨5094397682853860382006139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27170120975220588704032741 5094397682853860382006139)
    ·
      refine ⟨7641596524280790573009209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5094397682853860382006139 7641596524280790573009209)
      ·
        refine ⟨5731197393210592929756907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7641596524280790573009209 5731197393210592929756907)
        ·
          refine ⟨8596796089815889394635361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5731197393210592929756907 8596796089815889394635361)
          ·
            refine ⟨6447597067361917045976521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8596796089815889394635361 6447597067361917045976521)
            ·
              refine ⟨4835697800521437784482391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6447597067361917045976521 4835697800521437784482391)
              ·
                refine ⟨7253546700782156676723587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4835697800521437784482391 7253546700782156676723587)
                ·
                  refine ⟨10880320051173235015085381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7253546700782156676723587 10880320051173235015085381)
                  ·
                    refine ⟨2040060009594981565328509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10880320051173235015085381 2040060009594981565328509)
                    ·
                      refine ⟨765022503598118086998191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2040060009594981565328509 765022503598118086998191)
                      ·
                        rfl

theorem cell23_1489876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_1489876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1489876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1489876 prefixEnd_1489876 := by exact prefixLift 1489876
  have htrace : WordTrace (prefixWord ++ tailWord_1489876) baseStart_1489876 baseEnd_1489876 := by
    simpa [prefixWord, tailWord_1489876, baseEnd_1489876] using wordTrace_append hprefix tailTrace_1489876
  have hstable : (prefixWord ++ tailWord_1489876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489876).length < 2 ^ (prefixWord ++ tailWord_1489876).sum := by decide
  have hdescent : baseEnd_1489876 < baseStart_1489876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489963 : List Nat := [1, 1, 1, 1, 2, 1, 6, 3, 3, 2, 2]
def baseStart_1489963 : Nat := 118140960795 + 1489963 * 2 ^ 59
def prefixEnd_1489963 : Nat := 4983230072969 + 3 ^ 40 * 1489963 * 2
def baseEnd_1489963 : Nat := 765067176415059246610291

theorem tailTrace_1489963 : CollatzResearch.WordTrace tailWord_1489963 prefixEnd_1489963 765067176415059246610291 := by
  unfold tailWord_1489963
  simp only [CollatzResearch.WordTrace]
  refine ⟨54343415101125991266482543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36228943400750660844321695 54343415101125991266482543)
  ·
    refine ⟨81515122651688986899723815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54343415101125991266482543 81515122651688986899723815)
    ·
      refine ⟨122272683977533480349585723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81515122651688986899723815 122272683977533480349585723)
      ·
        refine ⟨183409025966300220524378585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122272683977533480349585723 183409025966300220524378585)
        ·
          refine ⟨137556769474725165393283939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183409025966300220524378585 137556769474725165393283939)
          ·
            refine ⟨206335154212087748089925909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137556769474725165393283939 206335154212087748089925909)
            ·
              refine ⟨9671960353691613191715277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 206335154212087748089925909 9671960353691613191715277)
              ·
                refine ⟨3626985132634354946893229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9671960353691613191715277 3626985132634354946893229)
                ·
                  refine ⟨1360119424737883105084961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3626985132634354946893229 1360119424737883105084961)
                  ·
                    refine ⟨1020089568553412328813721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1360119424737883105084961 1020089568553412328813721)
                    ·
                      refine ⟨765067176415059246610291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1020089568553412328813721 765067176415059246610291)
                      ·
                        rfl

theorem cell23_1489963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3, 3, 2, 2].length) (baseStart_1489963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1489963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1489963 prefixEnd_1489963 := by exact prefixLift 1489963
  have htrace : WordTrace (prefixWord ++ tailWord_1489963) baseStart_1489963 baseEnd_1489963 := by
    simpa [prefixWord, tailWord_1489963, baseEnd_1489963] using wordTrace_append hprefix tailTrace_1489963
  have hstable : (prefixWord ++ tailWord_1489963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489963).length < 2 ^ (prefixWord ++ tailWord_1489963).sum := by decide
  have hdescent : baseEnd_1489963 < baseStart_1489963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489966 : List Nat := [4, 1, 3, 1, 1, 1, 2, 1, 3, 1, 5]
def baseStart_1489966 : Nat := 118140960795 + 1489966 * 2 ^ 59
def prefixEnd_1489966 : Nat := 4983230072969 + 3 ^ 40 * 1489966 * 2
def baseEnd_1489966 : Nat := 765068716857022734872777

theorem tailTrace_1489966 : CollatzResearch.WordTrace tailWord_1489966 prefixEnd_1489966 765068716857022734872777 := by
  unfold tailWord_1489966
  simp only [CollatzResearch.WordTrace]
  refine ⟨6792940565014390347355219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36229016346743415185894501 6792940565014390347355219)
  ·
    refine ⟨10189410847521585521032829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6792940565014390347355219 10189410847521585521032829)
    ·
      refine ⟨3821029067820594570387311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10189410847521585521032829 3821029067820594570387311)
      ·
        refine ⟨5731543601730891855580967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3821029067820594570387311 5731543601730891855580967)
        ·
          refine ⟨8597315402596337783371451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5731543601730891855580967 8597315402596337783371451)
          ·
            refine ⟨12895973103894506675057177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8597315402596337783371451 12895973103894506675057177)
            ·
              refine ⟨9671979827920880006292883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12895973103894506675057177 9671979827920880006292883)
              ·
                refine ⟨14507969741881320009439325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9671979827920880006292883 14507969741881320009439325)
                ·
                  refine ⟨5440488653205495003539747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14507969741881320009439325 5440488653205495003539747)
                  ·
                    refine ⟨8160732979808242505309621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5440488653205495003539747 8160732979808242505309621)
                    ·
                      refine ⟨765068716857022734872777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8160732979808242505309621 765068716857022734872777)
                      ·
                        rfl

theorem cell23_1489966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_1489966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1489966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1489966 prefixEnd_1489966 := by exact prefixLift 1489966
  have htrace : WordTrace (prefixWord ++ tailWord_1489966) baseStart_1489966 baseEnd_1489966 := by
    simpa [prefixWord, tailWord_1489966, baseEnd_1489966] using wordTrace_append hprefix tailTrace_1489966
  have hstable : (prefixWord ++ tailWord_1489966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489966).length < 2 ^ (prefixWord ++ tailWord_1489966).sum := by decide
  have hdescent : baseEnd_1489966 < baseStart_1489966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489976 : List Nat := [2, 1, 2, 1, 5, 1, 1, 3, 1, 2, 4]
def baseStart_1489976 : Nat := 118140960795 + 1489976 * 2 ^ 59
def prefixEnd_1489976 : Nat := 4983230072969 + 3 ^ 40 * 1489976 * 2
def baseEnd_1489976 : Nat := 765073851663567695747731

theorem tailTrace_1489976 : CollatzResearch.WordTrace tailWord_1489976 prefixEnd_1489976 765073851663567695747731 := by
  unfold tailWord_1489976
  simp only [CollatzResearch.WordTrace]
  refine ⟨27171944625039447243352891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36229259500052596324470521 27171944625039447243352891)
  ·
    refine ⟨40757916937559170865029337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27171944625039447243352891 40757916937559170865029337)
    ·
      refine ⟨30568437703169378148772003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40757916937559170865029337 30568437703169378148772003)
      ·
        refine ⟨45852656554754067223158005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30568437703169378148772003 45852656554754067223158005)
        ·
          refine ⟨4298686552008193802171063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45852656554754067223158005 4298686552008193802171063)
          ·
            refine ⟨6448029828012290703256595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4298686552008193802171063 6448029828012290703256595)
            ·
              refine ⟨9672044742018436054884893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6448029828012290703256595 9672044742018436054884893)
              ·
                refine ⟨3627016778256913520581835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9672044742018436054884893 3627016778256913520581835)
                ·
                  refine ⟨5440525167385370280872753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3627016778256913520581835 5440525167385370280872753)
                  ·
                    refine ⟨4080393875539027710654565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5440525167385370280872753 4080393875539027710654565)
                    ·
                      refine ⟨765073851663567695747731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4080393875539027710654565 765073851663567695747731)
                      ·
                        rfl

theorem cell23_1489976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3, 1, 2, 4].length) (baseStart_1489976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1489976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1489976 prefixEnd_1489976 := by exact prefixLift 1489976
  have htrace : WordTrace (prefixWord ++ tailWord_1489976) baseStart_1489976 baseEnd_1489976 := by
    simpa [prefixWord, tailWord_1489976, baseEnd_1489976] using wordTrace_append hprefix tailTrace_1489976
  have hstable : (prefixWord ++ tailWord_1489976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489976).length < 2 ^ (prefixWord ++ tailWord_1489976).sum := by decide
  have hdescent : baseEnd_1489976 < baseStart_1489976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489980 : List Nat := [2, 2, 2, 2, 2, 3, 1, 2, 3, 2, 2]
def baseStart_1489980 : Nat := 118140960795 + 1489980 * 2 ^ 59
def prefixEnd_1489980 : Nat := 4983230072969 + 3 ^ 40 * 1489980 * 2
def baseEnd_1489980 : Nat := 765075905586185680097713

theorem tailTrace_1489980 : CollatzResearch.WordTrace tailWord_1489980 prefixEnd_1489980 765075905586185680097713 := by
  unfold tailWord_1489980
  simp only [CollatzResearch.WordTrace]
  refine ⟨27172017571032201584925697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36229356761376268779900929 27172017571032201584925697)
  ·
    refine ⟨20379013178274151188694273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27172017571032201584925697 20379013178274151188694273)
    ·
      refine ⟨15284259883705613391520705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20379013178274151188694273 15284259883705613391520705)
      ·
        refine ⟨11463194912779210043640529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15284259883705613391520705 11463194912779210043640529)
        ·
          refine ⟨8597396184584407532730397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11463194912779210043640529 8597396184584407532730397)
          ·
            refine ⟨3224023569219152824773899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8597396184584407532730397 3224023569219152824773899)
            ·
              refine ⟨4836035353828729237160849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3224023569219152824773899 4836035353828729237160849)
              ·
                refine ⟨3627026515371546927870637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4836035353828729237160849 3627026515371546927870637)
                ·
                  refine ⟨1360134943264330097951489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3627026515371546927870637 1360134943264330097951489)
                  ·
                    refine ⟨1020101207448247573463617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1360134943264330097951489 1020101207448247573463617)
                    ·
                      refine ⟨765075905586185680097713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1020101207448247573463617 765075905586185680097713)
                      ·
                        rfl

theorem cell23_1489980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 2, 3, 2, 2].length) (baseStart_1489980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1489980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1489980 prefixEnd_1489980 := by exact prefixLift 1489980
  have htrace : WordTrace (prefixWord ++ tailWord_1489980) baseStart_1489980 baseEnd_1489980 := by
    simpa [prefixWord, tailWord_1489980, baseEnd_1489980] using wordTrace_append hprefix tailTrace_1489980
  have hstable : (prefixWord ++ tailWord_1489980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489980).length < 2 ^ (prefixWord ++ tailWord_1489980).sum := by decide
  have hdescent : baseEnd_1489980 < baseStart_1489980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489997 : List Nat := [1, 6, 1, 1, 1, 4, 2, 1, 1, 1, 4]
def baseStart_1489997 : Nat := 118140960795 + 1489997 * 2 ^ 59
def prefixEnd_1489997 : Nat := 4983230072969 + 3 ^ 40 * 1489997 * 2
def baseEnd_1489997 : Nat := 765084634757312113585135

theorem tailTrace_1489997 : CollatzResearch.WordTrace tailWord_1489997 prefixEnd_1489997 765084634757312113585135 := by
  unfold tailWord_1489997
  simp only [CollatzResearch.WordTrace]
  refine ⟨54344655183002815073220245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36229770122001876715480163 54344655183002815073220245)
  ·
    refine ⟨2547405711703256956557199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 54344655183002815073220245 2547405711703256956557199)
    ·
      refine ⟨3821108567554885434835799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2547405711703256956557199 3821108567554885434835799)
      ·
        refine ⟨5731662851332328152253699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3821108567554885434835799 5731662851332328152253699)
        ·
          refine ⟨8597494276998492228380549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5731662851332328152253699 8597494276998492228380549)
          ·
            refine ⟨1612030176937217292821353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8597494276998492228380549 1612030176937217292821353)
            ·
              refine ⟨1209022632702912969616015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1612030176937217292821353 1209022632702912969616015)
              ·
                refine ⟨1813533949054369454424023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1209022632702912969616015 1813533949054369454424023)
                ·
                  refine ⟨2720300923581554181636035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1813533949054369454424023 2720300923581554181636035)
                  ·
                    refine ⟨4080451385372331272454053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2720300923581554181636035 4080451385372331272454053)
                    ·
                      refine ⟨765084634757312113585135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4080451385372331272454053 765084634757312113585135)
                      ·
                        rfl

theorem cell23_1489997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_1489997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1489997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1489997 prefixEnd_1489997 := by exact prefixLift 1489997
  have htrace : WordTrace (prefixWord ++ tailWord_1489997) baseStart_1489997 baseEnd_1489997 := by
    simpa [prefixWord, tailWord_1489997, baseEnd_1489997] using wordTrace_append hprefix tailTrace_1489997
  have hstable : (prefixWord ++ tailWord_1489997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489997).length < 2 ^ (prefixWord ++ tailWord_1489997).sum := by decide
  have hdescent : baseEnd_1489997 < baseStart_1489997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490009 : List Nat := [1, 2, 1, 2, 2, 1, 2, 1, 4, 2, 5]
def baseStart_1490009 : Nat := 118140960795 + 1490009 * 2 ^ 59
def prefixEnd_1490009 : Nat := 4983230072969 + 3 ^ 40 * 1490009 * 2
def baseEnd_1490009 : Nat := 765090796525166066635079

theorem tailTrace_1490009 : CollatzResearch.WordTrace tailWord_1490009 prefixEnd_1490009 765090796525166066635079 := by
  unfold tailWord_1490009
  simp only [CollatzResearch.WordTrace]
  refine ⟨54345092858959341122657081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36230061905972894081771387 54345092858959341122657081)
  ·
    refine ⟨40758819644219505841992811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54345092858959341122657081 40758819644219505841992811)
    ·
      refine ⟨61138229466329258762989217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40758819644219505841992811 61138229466329258762989217)
      ·
        refine ⟨45853672099746944072241913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61138229466329258762989217 45853672099746944072241913)
        ·
          refine ⟨34390254074810208054181435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45853672099746944072241913 34390254074810208054181435)
          ·
            refine ⟨51585381112215312081272153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34390254074810208054181435 51585381112215312081272153)
            ·
              refine ⟨38689035834161484060954115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51585381112215312081272153 38689035834161484060954115)
              ·
                refine ⟨58033553751242226091431173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38689035834161484060954115 58033553751242226091431173)
                ·
                  refine ⟨10881291328357917392143345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58033553751242226091431173 10881291328357917392143345)
                  ·
                    refine ⟨8160968496268438044107509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10881291328357917392143345 8160968496268438044107509)
                    ·
                      refine ⟨765090796525166066635079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8160968496268438044107509 765090796525166066635079)
                      ·
                        rfl

theorem cell23_1490009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 2, 5].length) (baseStart_1490009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1490009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1490009 prefixEnd_1490009 := by exact prefixLift 1490009
  have htrace : WordTrace (prefixWord ++ tailWord_1490009) baseStart_1490009 baseEnd_1490009 := by
    simpa [prefixWord, tailWord_1490009, baseEnd_1490009] using wordTrace_append hprefix tailTrace_1490009
  have hstable : (prefixWord ++ tailWord_1490009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490009).length < 2 ^ (prefixWord ++ tailWord_1490009).sum := by decide
  have hdescent : baseEnd_1490009 < baseStart_1490009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490014 : List Nat := [4, 4, 1, 1, 1, 1, 1, 3, 3, 2, 2]
def baseStart_1490014 : Nat := 118140960795 + 1490014 * 2 ^ 59
def prefixEnd_1490014 : Nat := 4983230072969 + 3 ^ 40 * 1490014 * 2
def baseEnd_1490014 : Nat := 765093363928438547072557

theorem tailTrace_1490014 : CollatzResearch.WordTrace tailWord_1490014 prefixEnd_1490014 765093363928438547072557 := by
  unfold tailWord_1490014
  simp only [CollatzResearch.WordTrace]
  refine ⟨6793159402992653372073637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36230183482627484651059397 6793159402992653372073637)
  ·
    refine ⟨1273717388061122507263807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6793159402992653372073637 1273717388061122507263807)
    ·
      refine ⟨1910576082091683760895711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1273717388061122507263807 1910576082091683760895711)
      ·
        refine ⟨2865864123137525641343567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1910576082091683760895711 2865864123137525641343567)
        ·
          refine ⟨4298796184706288462015351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2865864123137525641343567 4298796184706288462015351)
          ·
            refine ⟨6448194277059432693023027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4298796184706288462015351 6448194277059432693023027)
            ·
              refine ⟨9672291415589149039534541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6448194277059432693023027 9672291415589149039534541)
              ·
                refine ⟨3627109280845930889825453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9672291415589149039534541 3627109280845930889825453)
                ·
                  refine ⟨1360165980317224083684545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3627109280845930889825453 1360165980317224083684545)
                  ·
                    refine ⟨1020124485237918062763409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1360165980317224083684545 1020124485237918062763409)
                    ·
                      refine ⟨765093363928438547072557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1020124485237918062763409 765093363928438547072557)
                      ·
                        rfl

theorem cell23_1490014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_1490014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1490014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1490014 prefixEnd_1490014 := by exact prefixLift 1490014
  have htrace : WordTrace (prefixWord ++ tailWord_1490014) baseStart_1490014 baseEnd_1490014 := by
    simpa [prefixWord, tailWord_1490014, baseEnd_1490014] using wordTrace_append hprefix tailTrace_1490014
  have hstable : (prefixWord ++ tailWord_1490014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490014).length < 2 ^ (prefixWord ++ tailWord_1490014).sum := by decide
  have hdescent : baseEnd_1490014 < baseStart_1490014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490030 : List Nat := [4, 1, 2, 2, 1, 4, 1, 1, 1, 3, 3]
def baseStart_1490030 : Nat := 118140960795 + 1490030 * 2 ^ 59
def prefixEnd_1490030 : Nat := 4983230072969 + 3 ^ 40 * 1490030 * 2
def baseEnd_1490030 : Nat := 765101579618910484472483

theorem tailTrace_1490030 : CollatzResearch.WordTrace tailWord_1490030 prefixEnd_1490030 765101579618910484472483 := by
  unfold tailWord_1490030
  simp only [CollatzResearch.WordTrace]
  refine ⟨6793232348985407713646443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36230572527922174472781029 6793232348985407713646443)
  ·
    refine ⟨10189848523478111570469665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6793232348985407713646443 10189848523478111570469665)
    ·
      refine ⟨7642386392608583677852249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10189848523478111570469665 7642386392608583677852249)
      ·
        refine ⟨5731789794456437758389187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7642386392608583677852249 5731789794456437758389187)
        ·
          refine ⟨8597684691684656637583781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5731789794456437758389187 8597684691684656637583781)
          ·
            refine ⟨1612065879690873119546959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8597684691684656637583781 1612065879690873119546959)
            ·
              refine ⟨2418098819536309679320439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1612065879690873119546959 2418098819536309679320439)
              ·
                refine ⟨3627148229304464518980659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2418098819536309679320439 3627148229304464518980659)
                ·
                  refine ⟨5440722343956696778470989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3627148229304464518980659 5440722343956696778470989)
                  ·
                    refine ⟨2040270878983761291926621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5440722343956696778470989 2040270878983761291926621)
                    ·
                      refine ⟨765101579618910484472483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2040270878983761291926621 765101579618910484472483)
                      ·
                        rfl

theorem cell23_1490030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_1490030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1490030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1490030 prefixEnd_1490030 := by exact prefixLift 1490030
  have htrace : WordTrace (prefixWord ++ tailWord_1490030) baseStart_1490030 baseEnd_1490030 := by
    simpa [prefixWord, tailWord_1490030, baseEnd_1490030] using wordTrace_append hprefix tailTrace_1490030
  have hstable : (prefixWord ++ tailWord_1490030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490030).length < 2 ^ (prefixWord ++ tailWord_1490030).sum := by decide
  have hdescent : baseEnd_1490030 < baseStart_1490030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490037 : List Nat := [1, 3, 4, 3, 2, 1, 2, 7]
def baseStart_1490037 : Nat := 118140960795 + 1490037 * 2 ^ 59
def prefixEnd_1490037 : Nat := 4983230072969 + 3 ^ 40 * 1490037 * 2
def baseEnd_1490037 : Nat := 28337228666055257669813

theorem tailTrace_1490037 : CollatzResearch.WordTrace tailWord_1490037 prefixEnd_1490037 28337228666055257669813 := by
  unfold tailWord_1490037
  simp only [CollatzResearch.WordTrace]
  refine ⟨54346114102857901904676365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36230742735238601269784243 54346114102857901904676365)
  ·
    refine ⟨20379792788571713214253637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54346114102857901904676365 20379792788571713214253637)
    ·
      refine ⟨3821211147857196227672557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20379792788571713214253637 3821211147857196227672557)
      ·
        refine ⟨1432954180446448585377209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3821211147857196227672557 1432954180446448585377209)
        ·
          refine ⟨1074715635334836439032907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1432954180446448585377209 1074715635334836439032907)
          ·
            refine ⟨1612073453002254658549361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1074715635334836439032907 1612073453002254658549361)
            ·
              refine ⟨1209055089751690993912021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1612073453002254658549361 1209055089751690993912021)
              ·
                refine ⟨28337228666055257669813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1209055089751690993912021 28337228666055257669813)
                ·
                  rfl

theorem cell23_1490037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 7].length) (baseStart_1490037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1490037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1490037 prefixEnd_1490037 := by exact prefixLift 1490037
  have htrace : WordTrace (prefixWord ++ tailWord_1490037) baseStart_1490037 baseEnd_1490037 := by
    simpa [prefixWord, tailWord_1490037, baseEnd_1490037] using wordTrace_append hprefix tailTrace_1490037
  have hstable : (prefixWord ++ tailWord_1490037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490037).length < 2 ^ (prefixWord ++ tailWord_1490037).sum := by decide
  have hdescent : baseEnd_1490037 < baseStart_1490037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490059 : List Nat := [1, 1, 1, 1, 4, 1, 1, 4, 9]
def baseStart_1490059 : Nat := 118140960795 + 1490059 * 2 ^ 59
def prefixEnd_1490059 : Nat := 4983230072969 + 3 ^ 40 * 1490059 * 2
def baseEnd_1490059 : Nat := 85012941173098985667761

theorem tailTrace_1490059 : CollatzResearch.WordTrace tailWord_1490059 prefixEnd_1490059 85012941173098985667761 := by
  unfold tailWord_1490059
  simp only [CollatzResearch.WordTrace]
  refine ⟨54346916508778199661977231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36231277672518799774651487 54346916508778199661977231)
  ·
    refine ⟨81520374763167299492965847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54346916508778199661977231 81520374763167299492965847)
    ·
      refine ⟨122280562144750949239448771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81520374763167299492965847 122280562144750949239448771)
      ·
        refine ⟨183420843217126423859173157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122280562144750949239448771 183420843217126423859173157)
        ·
          refine ⟨34391408103211204473594967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 183420843217126423859173157 34391408103211204473594967)
          ·
            refine ⟨51587112154816806710392451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34391408103211204473594967 51587112154816806710392451)
            ·
              refine ⟨77380668232225210065588677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51587112154816806710392451 77380668232225210065588677)
              ·
                refine ⟨14508875293542226887297877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77380668232225210065588677 14508875293542226887297877)
                ·
                  refine ⟨85012941173098985667761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 14508875293542226887297877 85012941173098985667761)
                  ·
                    rfl

theorem cell23_1490059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 9].length) (baseStart_1490059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1490059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1490059 prefixEnd_1490059 := by exact prefixLift 1490059
  have htrace : WordTrace (prefixWord ++ tailWord_1490059) baseStart_1490059 baseEnd_1490059 := by
    simpa [prefixWord, tailWord_1490059, baseEnd_1490059] using wordTrace_append hprefix tailTrace_1490059
  have hstable : (prefixWord ++ tailWord_1490059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490059).length < 2 ^ (prefixWord ++ tailWord_1490059).sum := by decide
  have hdescent : baseEnd_1490059 < baseStart_1490059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490133 : List Nat := [1, 3, 2, 4, 1, 1, 2, 1, 1, 2, 5]
def baseStart_1490133 : Nat := 118140960795 + 1490133 * 2 ^ 59
def prefixEnd_1490133 : Nat := 4983230072969 + 3 ^ 40 * 1490133 * 2
def baseEnd_1490133 : Nat := 765154468126323581484509

theorem tailTrace_1490133 : CollatzResearch.WordTrace tailWord_1490133 prefixEnd_1490133 765154468126323581484509 := by
  unfold tailWord_1490133
  simp only [CollatzResearch.WordTrace]
  refine ⟨54349615510510110300171053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36233077007006740200114035 54349615510510110300171053)
  ·
    refine ⟨20381105816441291362564145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54349615510510110300171053 20381105816441291362564145)
    ·
      refine ⟨15285829362330968521923109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20381105816441291362564145 15285829362330968521923109)
      ·
        refine ⟨2866093005437056597860583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15285829362330968521923109 2866093005437056597860583)
        ·
          refine ⟨4299139508155584896790875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2866093005437056597860583 4299139508155584896790875)
          ·
            refine ⟨6448709262233377345186313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4299139508155584896790875 6448709262233377345186313)
            ·
              refine ⟨4836531946675033008889735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6448709262233377345186313 4836531946675033008889735)
              ·
                refine ⟨7254797920012549513334603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4836531946675033008889735 7254797920012549513334603)
                ·
                  refine ⟨10882196880018824270001905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7254797920012549513334603 10882196880018824270001905)
                  ·
                    refine ⟨8161647660014118202501429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10882196880018824270001905 8161647660014118202501429)
                    ·
                      refine ⟨765154468126323581484509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8161647660014118202501429 765154468126323581484509)
                      ·
                        rfl

theorem cell23_1490133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_1490133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1490133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1490133 prefixEnd_1490133 := by exact prefixLift 1490133
  have htrace : WordTrace (prefixWord ++ tailWord_1490133) baseStart_1490133 baseEnd_1490133 := by
    simpa [prefixWord, tailWord_1490133, baseEnd_1490133] using wordTrace_append hprefix tailTrace_1490133
  have hstable : (prefixWord ++ tailWord_1490133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490133).length < 2 ^ (prefixWord ++ tailWord_1490133).sum := by decide
  have hdescent : baseEnd_1490133 < baseStart_1490133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490143 : List Nat := [1, 1, 2, 3, 2, 1, 3, 1, 1, 6, 2]
def baseStart_1490143 : Nat := 118140960795 + 1490143 * 2 ^ 59
def prefixEnd_1490143 : Nat := 4983230072969 + 3 ^ 40 * 1490143 * 2
def baseEnd_1490143 : Nat := 765159602932868542359463

theorem tailTrace_1490143 : CollatzResearch.WordTrace tailWord_1490143 prefixEnd_1490143 765159602932868542359463 := by
  unfold tailWord_1490143
  simp only [CollatzResearch.WordTrace]
  refine ⟨54349980240473882008035083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36233320160315921338690055 54349980240473882008035083)
  ·
    refine ⟨81524970360710823012052625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54349980240473882008035083 81524970360710823012052625)
    ·
      refine ⟨61143727770533117259039469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81524970360710823012052625 61143727770533117259039469)
      ·
        refine ⟨22928897913949918972139801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61143727770533117259039469 22928897913949918972139801)
        ·
          refine ⟨17196673435462439229104851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22928897913949918972139801 17196673435462439229104851)
          ·
            refine ⟨25795010153193658843657277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17196673435462439229104851 25795010153193658843657277)
            ·
              refine ⟨9673128807447622066371479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25795010153193658843657277 9673128807447622066371479)
              ·
                refine ⟨14509693211171433099557219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9673128807447622066371479 14509693211171433099557219)
                ·
                  refine ⟨21764539816757149649335829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14509693211171433099557219 21764539816757149649335829)
                  ·
                    refine ⟨1020212803910491389812617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21764539816757149649335829 1020212803910491389812617)
                    ·
                      refine ⟨765159602932868542359463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1020212803910491389812617 765159602932868542359463)
                      ·
                        rfl

theorem cell23_1490143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 6, 2].length) (baseStart_1490143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1490143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1490143 prefixEnd_1490143 := by exact prefixLift 1490143
  have htrace : WordTrace (prefixWord ++ tailWord_1490143) baseStart_1490143 baseEnd_1490143 := by
    simpa [prefixWord, tailWord_1490143, baseEnd_1490143] using wordTrace_append hprefix tailTrace_1490143
  have hstable : (prefixWord ++ tailWord_1490143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490143).length < 2 ^ (prefixWord ++ tailWord_1490143).sum := by decide
  have hdescent : baseEnd_1490143 < baseStart_1490143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490163 : List Nat := [1, 1, 1, 2, 2, 6, 1, 1, 1, 4, 3]
def baseStart_1490163 : Nat := 118140960795 + 1490163 * 2 ^ 59
def prefixEnd_1490163 : Nat := 4983230072969 + 3 ^ 40 * 1490163 * 2
def baseEnd_1490163 : Nat := 765169872545958464109371

theorem tailTrace_1490163 : CollatzResearch.WordTrace tailWord_1490163 prefixEnd_1490163 765169872545958464109371 := by
  unfold tailWord_1490163
  simp only [CollatzResearch.WordTrace]
  refine ⟨54350709700401425423763143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36233806466934283615842095 54350709700401425423763143)
  ·
    refine ⟨81526064550602138135644715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54350709700401425423763143 81526064550602138135644715)
    ·
      refine ⟨122289096825903207203467073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81526064550602138135644715 122289096825903207203467073)
      ·
        refine ⟨91716822619427405402600305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122289096825903207203467073 91716822619427405402600305)
        ·
          refine ⟨68787616964570554051950229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91716822619427405402600305 68787616964570554051950229)
          ·
            refine ⟨3224419545214244721185167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 68787616964570554051950229 3224419545214244721185167)
            ·
              refine ⟨4836629317821367081777751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3224419545214244721185167 4836629317821367081777751)
              ·
                refine ⟨7254943976732050622666627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4836629317821367081777751 7254943976732050622666627)
                ·
                  refine ⟨10882415965098075933999941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7254943976732050622666627 10882415965098075933999941)
                  ·
                    refine ⟨2040452993455889237624989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10882415965098075933999941 2040452993455889237624989)
                    ·
                      refine ⟨765169872545958464109371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2040452993455889237624989 765169872545958464109371)
                      ·
                        rfl

theorem cell23_1490163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 4, 3].length) (baseStart_1490163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1490163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1490163 prefixEnd_1490163 := by exact prefixLift 1490163
  have htrace : WordTrace (prefixWord ++ tailWord_1490163) baseStart_1490163 baseEnd_1490163 := by
    simpa [prefixWord, tailWord_1490163, baseEnd_1490163] using wordTrace_append hprefix tailTrace_1490163
  have hstable : (prefixWord ++ tailWord_1490163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490163).length < 2 ^ (prefixWord ++ tailWord_1490163).sum := by decide
  have hdescent : baseEnd_1490163 < baseStart_1490163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490200 : List Nat := [2, 1, 2, 3, 1, 4, 3, 1, 6]
def baseStart_1490200 : Nat := 118140960795 + 1490200 * 2 ^ 59
def prefixEnd_1490200 : Nat := 4983230072969 + 3 ^ 40 * 1490200 * 2
def baseEnd_1490200 : Nat := 85020985703352757705189

theorem tailTrace_1490200 : CollatzResearch.WordTrace tailWord_1490200 prefixEnd_1490200 85020985703352757705189 := by
  unfold tailWord_1490200
  simp only [CollatzResearch.WordTrace]
  refine ⟨27176029600633690371430027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36234706134178253828573369 27176029600633690371430027)
  ·
    refine ⟨40764044400950535557145041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27176029600633690371430027 40764044400950535557145041)
    ·
      refine ⟨30573033300712901667858781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40764044400950535557145041 30573033300712901667858781)
      ·
        refine ⟨11464887487767338125447043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30573033300712901667858781 11464887487767338125447043)
        ·
          refine ⟨17197331231651007188170565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11464887487767338125447043 17197331231651007188170565)
          ·
            refine ⟨3224499605934563847781981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17197331231651007188170565 3224499605934563847781981)
            ·
              refine ⟨1209187352225461442918243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3224499605934563847781981 1209187352225461442918243)
              ·
                refine ⟨1813781028338192164377365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1209187352225461442918243 1813781028338192164377365)
                ·
                  refine ⟨85020985703352757705189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1813781028338192164377365 85020985703352757705189)
                  ·
                    rfl

theorem cell23_1490200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 1, 6].length) (baseStart_1490200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1490200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1490200 prefixEnd_1490200 := by exact prefixLift 1490200
  have htrace : WordTrace (prefixWord ++ tailWord_1490200) baseStart_1490200 baseEnd_1490200 := by
    simpa [prefixWord, tailWord_1490200, baseEnd_1490200] using wordTrace_append hprefix tailTrace_1490200
  have hstable : (prefixWord ++ tailWord_1490200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490200).length < 2 ^ (prefixWord ++ tailWord_1490200).sum := by decide
  have hdescent : baseEnd_1490200 < baseStart_1490200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490220 : List Nat := [2, 2, 1, 1, 1, 3, 1, 5, 2, 3, 2]
def baseStart_1490220 : Nat := 118140960795 + 1490220 * 2 ^ 59
def prefixEnd_1490220 : Nat := 4983230072969 + 3 ^ 40 * 1490220 * 2
def baseEnd_1490220 : Nat := 765199140943264741096609

theorem tailTrace_1490220 : CollatzResearch.WordTrace tailWord_1490220 prefixEnd_1490220 765199140943264741096609 := by
  unfold tailWord_1490220
  simp only [CollatzResearch.WordTrace]
  refine ⟨27176394330597462079294057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36235192440796616105725409 27176394330597462079294057)
  ·
    refine ⟨20382295747948096559470543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27176394330597462079294057 20382295747948096559470543)
    ·
      refine ⟨30573443621922144839205815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20382295747948096559470543 30573443621922144839205815)
      ·
        refine ⟨45860165432883217258808723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30573443621922144839205815 45860165432883217258808723)
        ·
          refine ⟨68790248149324825888213085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45860165432883217258808723 68790248149324825888213085)
          ·
            refine ⟨25796343055996809708079907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68790248149324825888213085 25796343055996809708079907)
            ·
              refine ⟨38694514583995214562119861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25796343055996809708079907 38694514583995214562119861)
              ·
                refine ⟨3627610742249551365198737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38694514583995214562119861 3627610742249551365198737)
                ·
                  refine ⟨2720708056687163523899053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3627610742249551365198737 2720708056687163523899053)
                  ·
                    refine ⟨1020265521257686321462145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2720708056687163523899053 1020265521257686321462145)
                    ·
                      refine ⟨765199140943264741096609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1020265521257686321462145 765199140943264741096609)
                      ·
                        rfl

theorem cell23_1490220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 3, 2].length) (baseStart_1490220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1490220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1490220 prefixEnd_1490220 := by exact prefixLift 1490220
  have htrace : WordTrace (prefixWord ++ tailWord_1490220) baseStart_1490220 baseEnd_1490220 := by
    simpa [prefixWord, tailWord_1490220, baseEnd_1490220] using wordTrace_append hprefix tailTrace_1490220
  have hstable : (prefixWord ++ tailWord_1490220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490220).length < 2 ^ (prefixWord ++ tailWord_1490220).sum := by decide
  have hdescent : baseEnd_1490220 < baseStart_1490220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490221 : List Nat := [1, 5, 3, 1, 1, 3, 1, 3, 1, 4]
def baseStart_1490221 : Nat := 118140960795 + 1490221 * 2 ^ 59
def prefixEnd_1490221 : Nat := 4983230072969 + 3 ^ 40 * 1490221 * 2
def baseEnd_1490221 : Nat := 255066551474639745728035

theorem tailTrace_1490221 : CollatzResearch.WordTrace tailWord_1490221 prefixEnd_1490221 255066551474639745728035 := by
  unfold tailWord_1490221
  simp only [CollatzResearch.WordTrace]
  refine ⟨54352825134191301329374517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36235216756127534219583011 54352825134191301329374517)
  ·
    refine ⟨5095577356330434499628861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54352825134191301329374517 5095577356330434499628861)
    ·
      refine ⟨1910841508623912937360823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5095577356330434499628861 1910841508623912937360823)
      ·
        refine ⟨2866262262935869406041235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1910841508623912937360823 2866262262935869406041235)
        ·
          refine ⟨4299393394403804109061853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2866262262935869406041235 4299393394403804109061853)
          ·
            refine ⟨1612272522901426540898195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4299393394403804109061853 1612272522901426540898195)
            ·
              refine ⟨2418408784352139811347293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1612272522901426540898195 2418408784352139811347293)
              ·
                refine ⟨906903294132052429255235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2418408784352139811347293 906903294132052429255235)
                ·
                  refine ⟨1360354941198078643882853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 906903294132052429255235 1360354941198078643882853)
                  ·
                    refine ⟨255066551474639745728035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1360354941198078643882853 255066551474639745728035)
                    ·
                      rfl

theorem cell23_1490221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_1490221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1490221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1490221 prefixEnd_1490221 := by exact prefixLift 1490221
  have htrace : WordTrace (prefixWord ++ tailWord_1490221) baseStart_1490221 baseEnd_1490221 := by
    simpa [prefixWord, tailWord_1490221, baseEnd_1490221] using wordTrace_append hprefix tailTrace_1490221
  have hstable : (prefixWord ++ tailWord_1490221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490221).length < 2 ^ (prefixWord ++ tailWord_1490221).sum := by decide
  have hdescent : baseEnd_1490221 < baseStart_1490221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490244 : List Nat := [2, 3, 4, 1, 1, 1, 3, 1, 3, 1, 3]
def baseStart_1490244 : Nat := 118140960795 + 1490244 * 2 ^ 59
def prefixEnd_1490244 : Nat := 4983230072969 + 3 ^ 40 * 1490244 * 2
def baseEnd_1490244 : Nat := 765211464478972647196499

theorem tailTrace_1490244 : CollatzResearch.WordTrace tailWord_1490244 prefixEnd_1490244 765211464478972647196499 := by
  unfold tailWord_1490244
  simp only [CollatzResearch.WordTrace]
  refine ⟨27176832006553988128730893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36235776008738650838307857 27176832006553988128730893)
  ·
    refine ⟨10191312002457745548274085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27176832006553988128730893 10191312002457745548274085)
    ·
      refine ⟨1910871000460827290301391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10191312002457745548274085 1910871000460827290301391)
      ·
        refine ⟨2866306500691240935452087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1910871000460827290301391 2866306500691240935452087)
        ·
          refine ⟨4299459751036861403178131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2866306500691240935452087 4299459751036861403178131)
          ·
            refine ⟨6449189626555292104767197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4299459751036861403178131 6449189626555292104767197)
            ·
              refine ⟨2418446109958234539287699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6449189626555292104767197 2418446109958234539287699)
              ·
                refine ⟨3627669164937351808931549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2418446109958234539287699 3627669164937351808931549)
                ·
                  refine ⟨1360375936851506928349331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3627669164937351808931549 1360375936851506928349331)
                  ·
                    refine ⟨2040563905277260392523997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1360375936851506928349331 2040563905277260392523997)
                    ·
                      refine ⟨765211464478972647196499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2040563905277260392523997 765211464478972647196499)
                      ·
                        rfl

theorem cell23_1490244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_1490244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1490244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1490244 prefixEnd_1490244 := by exact prefixLift 1490244
  have htrace : WordTrace (prefixWord ++ tailWord_1490244) baseStart_1490244 baseEnd_1490244 := by
    simpa [prefixWord, tailWord_1490244, baseEnd_1490244] using wordTrace_append hprefix tailTrace_1490244
  have hstable : (prefixWord ++ tailWord_1490244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490244).length < 2 ^ (prefixWord ++ tailWord_1490244).sum := by decide
  have hdescent : baseEnd_1490244 < baseStart_1490244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490263 : List Nat := [1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 6]
def baseStart_1490263 : Nat := 118140960795 + 1490263 * 2 ^ 59
def prefixEnd_1490263 : Nat := 4983230072969 + 3 ^ 40 * 1490263 * 2
def baseEnd_1490263 : Nat := 765221220611408072858911

theorem tailTrace_1490263 : CollatzResearch.WordTrace tailWord_1490263 prefixEnd_1490263 765221220611408072858911 := by
  unfold tailWord_1490263
  simp only [CollatzResearch.WordTrace]
  refine ⟨54354357000039142502403443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36236238000026095001602295 54354357000039142502403443)
  ·
    refine ⟨81531535500058713753605165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54354357000039142502403443 81531535500058713753605165)
    ·
      refine ⟨30574325812522017657601937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81531535500058713753605165 30574325812522017657601937)
      ·
        refine ⟨22930744359391513243201453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30574325812522017657601937 22930744359391513243201453)
        ·
          refine ⟨8599029134771817466200545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22930744359391513243201453 8599029134771817466200545)
          ·
            refine ⟨6449271851078863099650409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8599029134771817466200545 6449271851078863099650409)
            ·
              refine ⟨4836953888309147324737807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6449271851078863099650409 4836953888309147324737807)
              ·
                refine ⟨7255430832463720987106711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4836953888309147324737807 7255430832463720987106711)
                ·
                  refine ⟨10883146248695581480660067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7255430832463720987106711 10883146248695581480660067)
                  ·
                    refine ⟨16324719373043372220990101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10883146248695581480660067 16324719373043372220990101)
                    ·
                      refine ⟨765221220611408072858911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16324719373043372220990101 765221220611408072858911)
                      ·
                        rfl

theorem cell23_1490263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_1490263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1490263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1490263 prefixEnd_1490263 := by exact prefixLift 1490263
  have htrace : WordTrace (prefixWord ++ tailWord_1490263) baseStart_1490263 baseEnd_1490263 := by
    simpa [prefixWord, tailWord_1490263, baseEnd_1490263] using wordTrace_append hprefix tailTrace_1490263
  have hstable : (prefixWord ++ tailWord_1490263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490263).length < 2 ^ (prefixWord ++ tailWord_1490263).sum := by decide
  have hdescent : baseEnd_1490263 < baseStart_1490263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490287 : List Nat := [1, 1, 2, 1, 3, 1, 7, 1, 1, 2, 3]
def baseStart_1490287 : Nat := 118140960795 + 1490287 * 2 ^ 59
def prefixEnd_1490287 : Nat := 4983230072969 + 3 ^ 40 * 1490287 * 2
def baseEnd_1490287 : Nat := 765233544147115978958801

theorem tailTrace_1490287 : CollatzResearch.WordTrace tailWord_1490287 prefixEnd_1490287 765233544147115978958801 := by
  unfold tailWord_1490287
  simp only [CollatzResearch.WordTrace]
  refine ⟨54355232351952194601277115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36236821567968129734184743 54355232351952194601277115)
  ·
    refine ⟨81532848527928291901915673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54355232351952194601277115 81532848527928291901915673)
    ·
      refine ⟨61149636395946218926436755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81532848527928291901915673 61149636395946218926436755)
      ·
        refine ⟨91724454593919328389655133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61149636395946218926436755 91724454593919328389655133)
        ·
          refine ⟨34396670472719748146120675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91724454593919328389655133 34396670472719748146120675)
          ·
            refine ⟨51595005709079622219181013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34396670472719748146120675 51595005709079622219181013)
            ·
              refine ⟨1209257946306553645762055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 51595005709079622219181013 1209257946306553645762055)
              ·
                refine ⟨1813886919459830468643083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1209257946306553645762055 1813886919459830468643083)
                ·
                  refine ⟨2720830379189745702964625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1813886919459830468643083 2720830379189745702964625)
                  ·
                    refine ⟨2040622784392309277223469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2720830379189745702964625 2040622784392309277223469)
                    ·
                      refine ⟨765233544147115978958801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2040622784392309277223469 765233544147115978958801)
                      ·
                        rfl

theorem cell23_1490287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 1, 1, 2, 3].length) (baseStart_1490287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1490287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1490287 prefixEnd_1490287 := by exact prefixLift 1490287
  have htrace : WordTrace (prefixWord ++ tailWord_1490287) baseStart_1490287 baseEnd_1490287 := by
    simpa [prefixWord, tailWord_1490287, baseEnd_1490287] using wordTrace_append hprefix tailTrace_1490287
  have hstable : (prefixWord ++ tailWord_1490287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490287).length < 2 ^ (prefixWord ++ tailWord_1490287).sum := by decide
  have hdescent : baseEnd_1490287 < baseStart_1490287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490327 : List Nat := [1, 1, 3, 3, 1, 1, 1, 6, 1, 3, 2]
def baseStart_1490327 : Nat := 118140960795 + 1490327 * 2 ^ 59
def prefixEnd_1490327 : Nat := 4983230072969 + 3 ^ 40 * 1490327 * 2
def baseEnd_1490327 : Nat := 765254083373295822458617

theorem tailTrace_1490327 : CollatzResearch.WordTrace tailWord_1490327 prefixEnd_1490327 765254083373295822458617 := by
  unfold tailWord_1490327
  simp only [CollatzResearch.WordTrace]
  refine ⟨54356691271807281432733235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36237794181204854288488823 54356691271807281432733235)
  ·
    refine ⟨81535036907710922149099853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54356691271807281432733235 81535036907710922149099853)
    ·
      refine ⟨30575638840391595805912445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81535036907710922149099853 30575638840391595805912445)
      ·
        refine ⟨11465864565146848427217167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30575638840391595805912445 11465864565146848427217167)
        ·
          refine ⟨17198796847720272640825751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11465864565146848427217167 17198796847720272640825751)
          ·
            refine ⟨25798195271580408961238627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17198796847720272640825751 25798195271580408961238627)
            ·
              refine ⟨38697292907370613441857941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25798195271580408961238627 38697292907370613441857941)
              ·
                refine ⟨1813935605032997505087091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38697292907370613441857941 1813935605032997505087091)
                ·
                  refine ⟨2720903407549496257630637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1813935605032997505087091 2720903407549496257630637)
                  ·
                    refine ⟨1020338777831061096611489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2720903407549496257630637 1020338777831061096611489)
                    ·
                      refine ⟨765254083373295822458617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1020338777831061096611489 765254083373295822458617)
                      ·
                        rfl

theorem cell23_1490327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 6, 1, 3, 2].length) (baseStart_1490327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1490327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1490327 prefixEnd_1490327 := by exact prefixLift 1490327
  have htrace : WordTrace (prefixWord ++ tailWord_1490327) baseStart_1490327 baseEnd_1490327 := by
    simpa [prefixWord, tailWord_1490327, baseEnd_1490327] using wordTrace_append hprefix tailTrace_1490327
  have hstable : (prefixWord ++ tailWord_1490327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490327).length < 2 ^ (prefixWord ++ tailWord_1490327).sum := by decide
  have hdescent : baseEnd_1490327 < baseStart_1490327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490380 : List Nat := [2, 2, 1, 4, 2, 1, 2, 2, 7]
def baseStart_1490380 : Nat := 118140960795 + 1490380 * 2 ^ 59
def prefixEnd_1490380 : Nat := 4983230072969 + 3 ^ 40 * 1490380 * 2
def baseEnd_1490380 : Nat := 85031255316442679455097

theorem tailTrace_1490380 : CollatzResearch.WordTrace tailWord_1490380 prefixEnd_1490380 85031255316442679455097 := by
  unfold tailWord_1490380
  simp only [CollatzResearch.WordTrace]
  refine ⟨27179312170307635742206297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36239082893743514322941729 27179312170307635742206297)
  ·
    refine ⟨20384484127730726806654723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27179312170307635742206297 20384484127730726806654723)
    ·
      refine ⟨30576726191596090209982085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20384484127730726806654723 30576726191596090209982085)
      ·
        refine ⟨5733136160924266914371641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30576726191596090209982085 5733136160924266914371641)
        ·
          refine ⟨4299852120693200185778731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5733136160924266914371641 4299852120693200185778731)
          ·
            refine ⟨6449778181039800278668097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4299852120693200185778731 6449778181039800278668097)
            ·
              refine ⟨4837333635779850209001073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6449778181039800278668097 4837333635779850209001073)
              ·
                refine ⟨3628000226834887656750805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4837333635779850209001073 3628000226834887656750805)
                ·
                  refine ⟨85031255316442679455097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3628000226834887656750805 85031255316442679455097)
                  ·
                    rfl

theorem cell23_1490380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2, 7].length) (baseStart_1490380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1490380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1490380 prefixEnd_1490380 := by exact prefixLift 1490380
  have htrace : WordTrace (prefixWord ++ tailWord_1490380) baseStart_1490380 baseEnd_1490380 := by
    simpa [prefixWord, tailWord_1490380, baseEnd_1490380] using wordTrace_append hprefix tailTrace_1490380
  have hstable : (prefixWord ++ tailWord_1490380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490380).length < 2 ^ (prefixWord ++ tailWord_1490380).sum := by decide
  have hdescent : baseEnd_1490380 < baseStart_1490380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490414 : List Nat := [4, 1, 2, 1, 2, 1, 5, 2, 5]
def baseStart_1490414 : Nat := 118140960795 + 1490414 * 2 ^ 59
def prefixEnd_1490414 : Nat := 4983230072969 + 3 ^ 40 * 1490414 * 2
def baseEnd_1490414 : Nat := 85033195132248553563413

theorem tailTrace_1490414 : CollatzResearch.WordTrace tailWord_1490414 prefixEnd_1490414 85033195132248553563413 := by
  unfold tailWord_1490414
  simp only [CollatzResearch.WordTrace]
  refine ⟨6794983052811511911393787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36239909614994730194100197 6794983052811511911393787)
  ·
    refine ⟨10192474579217267867090681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6794983052811511911393787 10192474579217267867090681)
    ·
      refine ⟨7644355934412950900318011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10192474579217267867090681 7644355934412950900318011)
      ·
        refine ⟨11466533901619426350477017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7644355934412950900318011 11466533901619426350477017)
        ·
          refine ⟨8599900426214569762857763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11466533901619426350477017 8599900426214569762857763)
          ·
            refine ⟨12899850639321854644286645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8599900426214569762857763 12899850639321854644286645)
            ·
              refine ⟨1209360997436423872901873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12899850639321854644286645 1209360997436423872901873)
              ·
                refine ⟨907020748077317904676405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1209360997436423872901873 907020748077317904676405)
                ·
                  refine ⟨85033195132248553563413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 907020748077317904676405 85033195132248553563413)
                  ·
                    rfl

theorem cell23_1490414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 2, 5].length) (baseStart_1490414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1490414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1490414 prefixEnd_1490414 := by exact prefixLift 1490414
  have htrace : WordTrace (prefixWord ++ tailWord_1490414) baseStart_1490414 baseEnd_1490414 := by
    simpa [prefixWord, tailWord_1490414, baseEnd_1490414] using wordTrace_append hprefix tailTrace_1490414
  have hstable : (prefixWord ++ tailWord_1490414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490414).length < 2 ^ (prefixWord ++ tailWord_1490414).sum := by decide
  have hdescent : baseEnd_1490414 < baseStart_1490414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490423 : List Nat := [1, 1, 3, 1, 1, 1, 1, 4, 2, 8]
def baseStart_1490423 : Nat := 118140960795 + 1490423 * 2 ^ 59
def prefixEnd_1490423 : Nat := 4983230072969 + 3 ^ 40 * 1490423 * 2
def baseEnd_1490423 : Nat := 255101125838709148952725

theorem tailTrace_1490423 : CollatzResearch.WordTrace tailWord_1490423 prefixEnd_1490423 255101125838709148952725 := by
  unfold tailWord_1490423
  simp only [CollatzResearch.WordTrace]
  refine ⟨54360192679459489828227923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36240128452972993218818615 54360192679459489828227923)
  ·
    refine ⟨81540289019189234742341885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54360192679459489828227923 81540289019189234742341885)
    ·
      refine ⟨30577608382195963028378207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81540289019189234742341885 30577608382195963028378207)
      ·
        refine ⟨45866412573293944542567311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30577608382195963028378207 45866412573293944542567311)
        ·
          refine ⟨68799618859940916813850967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45866412573293944542567311 68799618859940916813850967)
          ·
            refine ⟨103199428289911375220776451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68799618859940916813850967 103199428289911375220776451)
            ·
              refine ⟨154799142434867062831164677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103199428289911375220776451 154799142434867062831164677)
              ·
                refine ⟨29024839206537574280843377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 154799142434867062831164677 29024839206537574280843377)
                ·
                  refine ⟨21768629404903180710632533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29024839206537574280843377 21768629404903180710632533)
                  ·
                    refine ⟨255101125838709148952725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 21768629404903180710632533 255101125838709148952725)
                    ·
                      rfl

theorem cell23_1490423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 8].length) (baseStart_1490423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1490423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1490423 prefixEnd_1490423 := by exact prefixLift 1490423
  have htrace : WordTrace (prefixWord ++ tailWord_1490423) baseStart_1490423 baseEnd_1490423 := by
    simpa [prefixWord, tailWord_1490423, baseEnd_1490423] using wordTrace_append hprefix tailTrace_1490423
  have hstable : (prefixWord ++ tailWord_1490423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490423).length < 2 ^ (prefixWord ++ tailWord_1490423).sum := by decide
  have hdescent : baseEnd_1490423 < baseStart_1490423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490460 : List Nat := [2, 2, 3, 1, 2, 1, 2, 1, 2, 1, 6]
def baseStart_1490460 : Nat := 118140960795 + 1490460 * 2 ^ 59
def prefixEnd_1490460 : Nat := 4983230072969 + 3 ^ 40 * 1490460 * 2
def baseEnd_1490460 : Nat := 765322376300343802095505

theorem tailTrace_1490460 : CollatzResearch.WordTrace tailWord_1490460 prefixEnd_1490460 765322376300343802095505 := by
  unfold tailWord_1490460
  simp only [CollatzResearch.WordTrace]
  refine ⟨27180771090162722573662417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36241028120216963431549889 27180771090162722573662417)
  ·
    refine ⟨20385578317622041930246813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27180771090162722573662417 20385578317622041930246813)
    ·
      refine ⟨7644591869108265723842555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20385578317622041930246813 7644591869108265723842555)
      ·
        refine ⟨11466887803662398585763833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7644591869108265723842555 11466887803662398585763833)
        ·
          refine ⟨8600165852746798939322875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11466887803662398585763833 8600165852746798939322875)
          ·
            refine ⟨12900248779120198408984313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8600165852746798939322875 12900248779120198408984313)
            ·
              refine ⟨9675186584340148806738235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12900248779120198408984313 9675186584340148806738235)
              ·
                refine ⟨14512779876510223210107353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9675186584340148806738235 14512779876510223210107353)
                ·
                  refine ⟨10884584907382667407580515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14512779876510223210107353 10884584907382667407580515)
                  ·
                    refine ⟨16326877361074001111370773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10884584907382667407580515 16326877361074001111370773)
                    ·
                      refine ⟨765322376300343802095505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16326877361074001111370773 765322376300343802095505)
                      ·
                        rfl

theorem cell23_1490460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_1490460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1490460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1490460 prefixEnd_1490460 := by exact prefixLift 1490460
  have htrace : WordTrace (prefixWord ++ tailWord_1490460) baseStart_1490460 baseEnd_1490460 := by
    simpa [prefixWord, tailWord_1490460, baseEnd_1490460] using wordTrace_append hprefix tailTrace_1490460
  have hstable : (prefixWord ++ tailWord_1490460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490460).length < 2 ^ (prefixWord ++ tailWord_1490460).sum := by decide
  have hdescent : baseEnd_1490460 < baseStart_1490460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490480 : List Nat := [2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 3]
def baseStart_1490480 : Nat := 118140960795 + 1490480 * 2 ^ 59
def prefixEnd_1490480 : Nat := 4983230072969 + 3 ^ 40 * 1490480 * 2
def baseEnd_1490480 : Nat := 765332645913433723845413

theorem tailTrace_1490480 : CollatzResearch.WordTrace tailWord_1490480 prefixEnd_1490480 765332645913433723845413 := by
  unfold tailWord_1490480
  simp only [CollatzResearch.WordTrace]
  refine ⟨27181135820126494281526447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36241514426835325708701929 27181135820126494281526447)
  ·
    refine ⟨40771703730189741422289671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27181135820126494281526447 40771703730189741422289671)
    ·
      refine ⟨61157555595284612133434507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40771703730189741422289671 61157555595284612133434507)
      ·
        refine ⟨91736333392926918200151761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61157555595284612133434507 91736333392926918200151761)
        ·
          refine ⟨68802250044695188650113821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91736333392926918200151761 68802250044695188650113821)
          ·
            refine ⟨25800843766760695743792683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68802250044695188650113821 25800843766760695743792683)
            ·
              refine ⟨38701265650141043615689025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25800843766760695743792683 38701265650141043615689025)
              ·
                refine ⟨29025949237605782711766769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38701265650141043615689025 29025949237605782711766769)
                ·
                  refine ⟨21769461928204337033825077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29025949237605782711766769 21769461928204337033825077)
                  ·
                    refine ⟨2040887055769156596921101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21769461928204337033825077 2040887055769156596921101)
                    ·
                      refine ⟨765332645913433723845413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2040887055769156596921101 765332645913433723845413)
                      ·
                        rfl

theorem cell23_1490480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 3].length) (baseStart_1490480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1490480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1490480 prefixEnd_1490480 := by exact prefixLift 1490480
  have htrace : WordTrace (prefixWord ++ tailWord_1490480) baseStart_1490480 baseEnd_1490480 := by
    simpa [prefixWord, tailWord_1490480, baseEnd_1490480] using wordTrace_append hprefix tailTrace_1490480
  have hstable : (prefixWord ++ tailWord_1490480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490480).length < 2 ^ (prefixWord ++ tailWord_1490480).sum := by decide
  have hdescent : baseEnd_1490480 < baseStart_1490480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490510 : List Nat := [4, 1, 1, 1, 1, 2, 1, 1, 2, 4, 5]
def baseStart_1490510 : Nat := 118140960795 + 1490510 * 2 ^ 59
def prefixEnd_1490510 : Nat := 4983230072969 + 3 ^ 40 * 1490510 * 2
def baseEnd_1490510 : Nat := 765348050333068606470275

theorem tailTrace_1490510 : CollatzResearch.WordTrace tailWord_1490510 prefixEnd_1490510 765348050333068606470275 := by
  unfold tailWord_1490510
  simp only [CollatzResearch.WordTrace]
  refine ⟨6795420728768037960830623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36242243886762869124429989 6795420728768037960830623)
  ·
    refine ⟨10193131093152056941245935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6795420728768037960830623 10193131093152056941245935)
    ·
      refine ⟨15289696639728085411868903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10193131093152056941245935 15289696639728085411868903)
      ·
        refine ⟨22934544959592128117803355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15289696639728085411868903 22934544959592128117803355)
        ·
          refine ⟨34401817439388192176705033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22934544959592128117803355 34401817439388192176705033)
          ·
            refine ⟨25801363079541144132528775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34401817439388192176705033 25801363079541144132528775)
            ·
              refine ⟨38702044619311716198793163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25801363079541144132528775 38702044619311716198793163)
              ·
                refine ⟨58053066928967574298189745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38702044619311716198793163 58053066928967574298189745)
                ·
                  refine ⟨43539800196725680723642309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58053066928967574298189745 43539800196725680723642309)
                  ·
                    refine ⟨8163712536886065135682933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43539800196725680723642309 8163712536886065135682933)
                    ·
                      refine ⟨765348050333068606470275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8163712536886065135682933 765348050333068606470275)
                      ·
                        rfl

theorem cell23_1490510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_1490510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1490510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1490510 prefixEnd_1490510 := by exact prefixLift 1490510
  have htrace : WordTrace (prefixWord ++ tailWord_1490510) baseStart_1490510 baseEnd_1490510 := by
    simpa [prefixWord, tailWord_1490510, baseEnd_1490510] using wordTrace_append hprefix tailTrace_1490510
  have hstable : (prefixWord ++ tailWord_1490510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490510).length < 2 ^ (prefixWord ++ tailWord_1490510).sum := by decide
  have hdescent : baseEnd_1490510 < baseStart_1490510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490531 : List Nat := [1, 1, 1, 5, 1, 3, 2, 4, 1, 1, 3]
def baseStart_1490531 : Nat := 118140960795 + 1490531 * 2 ^ 59
def prefixEnd_1490531 : Nat := 4983230072969 + 3 ^ 40 * 1490531 * 2
def baseEnd_1490531 : Nat := 765358833426813024307679

theorem tailTrace_1490531 : CollatzResearch.WordTrace tailWord_1490531 prefixEnd_1490531 765358833426813024307679 := by
  unfold tailWord_1490531
  simp only [CollatzResearch.WordTrace]
  refine ⟨54364131763068224273159447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36242754508712149515439631 54364131763068224273159447)
  ·
    refine ⟨81546197644602336409739171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54364131763068224273159447 81546197644602336409739171)
    ·
      refine ⟨122319296466903504614608757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81546197644602336409739171 122319296466903504614608757)
      ·
        refine ⟨11467434043772203557619571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 122319296466903504614608757 11467434043772203557619571)
        ·
          refine ⟨17201151065658305336429357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11467434043772203557619571 17201151065658305336429357)
          ·
            refine ⟨6450431649621864501161009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17201151065658305336429357 6450431649621864501161009)
            ·
              refine ⟨4837823737216398375870757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6450431649621864501161009 4837823737216398375870757)
              ·
                refine ⟨907091950728074695475767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4837823737216398375870757 907091950728074695475767)
                ·
                  refine ⟨1360637926092112043213651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 907091950728074695475767 1360637926092112043213651)
                  ·
                    refine ⟨2040956889138168064820477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1360637926092112043213651 2040956889138168064820477)
                    ·
                      refine ⟨765358833426813024307679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2040956889138168064820477 765358833426813024307679)
                      ·
                        rfl

theorem cell23_1490531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 4, 1, 1, 3].length) (baseStart_1490531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1490531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1490531 prefixEnd_1490531 := by exact prefixLift 1490531
  have htrace : WordTrace (prefixWord ++ tailWord_1490531) baseStart_1490531 baseEnd_1490531 := by
    simpa [prefixWord, tailWord_1490531, baseEnd_1490531] using wordTrace_append hprefix tailTrace_1490531
  have hstable : (prefixWord ++ tailWord_1490531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490531).length < 2 ^ (prefixWord ++ tailWord_1490531).sum := by decide
  have hdescent : baseEnd_1490531 < baseStart_1490531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490554 : List Nat := [3, 1, 1, 1, 1, 1, 1, 5, 5, 2, 2]
def baseStart_1490554 : Nat := 118140960795 + 1490554 * 2 ^ 59
def prefixEnd_1490554 : Nat := 4983230072969 + 3 ^ 40 * 1490554 * 2
def baseEnd_1490554 : Nat := 765370643481866434320073

theorem tailTrace_1490554 : CollatzResearch.WordTrace tailWord_1490554 prefixEnd_1490554 765370643481866434320073 := by
  unfold tailWord_1490554
  simp only [CollatzResearch.WordTrace]
  refine ⟨13591242660496224800311679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36243313761323266134164477 13591242660496224800311679)
  ·
    refine ⟨20386863990744337200467519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13591242660496224800311679 20386863990744337200467519)
    ·
      refine ⟨30580295986116505800701279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20386863990744337200467519 30580295986116505800701279)
      ·
        refine ⟨45870443979174758701051919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30580295986116505800701279 45870443979174758701051919)
        ·
          refine ⟨68805665968762138051577879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45870443979174758701051919 68805665968762138051577879)
          ·
            refine ⟨103208498953143207077366819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68805665968762138051577879 103208498953143207077366819)
            ·
              refine ⟨154812748429714810616050229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103208498953143207077366819 154812748429714810616050229)
              ·
                refine ⟨14513695165285763495254709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 154812748429714810616050229 14513695165285763495254709)
                ·
                  refine ⟨1360658921745540327680129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14513695165285763495254709 1360658921745540327680129)
                  ·
                    refine ⟨1020494191309155245760097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1360658921745540327680129 1020494191309155245760097)
                    ·
                      refine ⟨765370643481866434320073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1020494191309155245760097 765370643481866434320073)
                      ·
                        rfl

theorem cell23_1490554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 5, 2, 2].length) (baseStart_1490554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1490554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1490554 prefixEnd_1490554 := by exact prefixLift 1490554
  have htrace : WordTrace (prefixWord ++ tailWord_1490554) baseStart_1490554 baseEnd_1490554 := by
    simpa [prefixWord, tailWord_1490554, baseEnd_1490554] using wordTrace_append hprefix tailTrace_1490554
  have hstable : (prefixWord ++ tailWord_1490554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490554).length < 2 ^ (prefixWord ++ tailWord_1490554).sum := by decide
  have hdescent : baseEnd_1490554 < baseStart_1490554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490560 : List Nat := [2, 1, 1, 2, 1, 4, 3, 9]
def baseStart_1490560 : Nat := 118140960795 + 1490560 * 2 ^ 59
def prefixEnd_1490560 : Nat := 4983230072969 + 3 ^ 40 * 1490560 * 2
def baseEnd_1490560 : Nat := 28347174976510867068335

theorem tailTrace_1490560 : CollatzResearch.WordTrace tailWord_1490560 prefixEnd_1490560 28347174976510867068335 := by
  unfold tailWord_1490560
  simp only [CollatzResearch.WordTrace]
  refine ⟨27182594739981581112982567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36243459653308774817310089 27182594739981581112982567)
  ·
    refine ⟨40773892109972371669473851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27182594739981581112982567 40773892109972371669473851)
    ·
      refine ⟨61160838164958557504210777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40773892109972371669473851 61160838164958557504210777)
      ·
        refine ⟨45870628623718918128158083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61160838164958557504210777 45870628623718918128158083)
        ·
          refine ⟨68805942935578377192237125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45870628623718918128158083 68805942935578377192237125)
          ·
            refine ⟨12901114300420945723544461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68805942935578377192237125 12901114300420945723544461)
            ·
              refine ⟨4837917862657854646329173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12901114300420945723544461 4837917862657854646329173)
              ·
                refine ⟨28347174976510867068335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4837917862657854646329173 28347174976510867068335)
                ·
                  rfl

theorem cell23_1490560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 9].length) (baseStart_1490560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1490560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1490560 prefixEnd_1490560 := by exact prefixLift 1490560
  have htrace : WordTrace (prefixWord ++ tailWord_1490560) baseStart_1490560 baseEnd_1490560 := by
    simpa [prefixWord, tailWord_1490560, baseEnd_1490560] using wordTrace_append hprefix tailTrace_1490560
  have hstable : (prefixWord ++ tailWord_1490560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490560).length < 2 ^ (prefixWord ++ tailWord_1490560).sum := by decide
  have hdescent : baseEnd_1490560 < baseStart_1490560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490574 : List Nat := [4, 1, 1, 3, 1, 3, 2, 1, 1, 1, 5]
def baseStart_1490574 : Nat := 118140960795 + 1490574 * 2 ^ 59
def prefixEnd_1490574 : Nat := 4983230072969 + 3 ^ 40 * 1490574 * 2
def baseEnd_1490574 : Nat := 765380913094956356069981

theorem tailTrace_1490574 : CollatzResearch.WordTrace tailWord_1490574 prefixEnd_1490574 765380913094956356069981 := by
  unfold tailWord_1490574
  simp only [CollatzResearch.WordTrace]
  refine ⟨6795712512739055327121847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36243800067941628411316517 6795712512739055327121847)
  ·
    refine ⟨10193568769108582990682771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6795712512739055327121847 10193568769108582990682771)
    ·
      refine ⟨15290353153662874486024157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10193568769108582990682771 15290353153662874486024157)
      ·
        refine ⟨5733882432623577932259059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15290353153662874486024157 5733882432623577932259059)
        ·
          refine ⟨8600823648935366898388589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5733882432623577932259059 8600823648935366898388589)
          ·
            refine ⟨3225308868350762586895721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8600823648935366898388589 3225308868350762586895721)
            ·
              refine ⟨2418981651263071940171791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3225308868350762586895721 2418981651263071940171791)
              ·
                refine ⟨3628472476894607910257687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2418981651263071940171791 3628472476894607910257687)
                ·
                  refine ⟨5442708715341911865386531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3628472476894607910257687 5442708715341911865386531)
                  ·
                    refine ⟨8164063073012867798079797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5442708715341911865386531 8164063073012867798079797)
                    ·
                      refine ⟨765380913094956356069981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8164063073012867798079797 765380913094956356069981)
                      ·
                        rfl

theorem cell23_1490574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_1490574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1490574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1490574 prefixEnd_1490574 := by exact prefixLift 1490574
  have htrace : WordTrace (prefixWord ++ tailWord_1490574) baseStart_1490574 baseEnd_1490574 := by
    simpa [prefixWord, tailWord_1490574, baseEnd_1490574] using wordTrace_append hprefix tailTrace_1490574
  have hstable : (prefixWord ++ tailWord_1490574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490574).length < 2 ^ (prefixWord ++ tailWord_1490574).sum := by decide
  have hdescent : baseEnd_1490574 < baseStart_1490574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490644 : List Nat := [2, 4, 1, 3, 1, 1, 1, 1, 2, 3, 4]
def baseStart_1490644 : Nat := 118140960795 + 1490644 * 2 ^ 59
def prefixEnd_1490644 : Nat := 4983230072969 + 3 ^ 40 * 1490644 * 2
def baseEnd_1490644 : Nat := 765416856740771082194659

theorem tailTrace_1490644 : CollatzResearch.WordTrace tailWord_1490644 prefixEnd_1490644 765416856740771082194659 := by
  unfold tailWord_1490644
  simp only [CollatzResearch.WordTrace]
  refine ⟨27184126605829422286011493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36245502141105896381348657 27184126605829422286011493)
  ·
    refine ⟨5097023738593016678627155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27184126605829422286011493 5097023738593016678627155)
    ·
      refine ⟨7645535607889525017940733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5097023738593016678627155 7645535607889525017940733)
      ·
        refine ⟨2867075852958571881727775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7645535607889525017940733 2867075852958571881727775)
        ·
          refine ⟨4300613779437857822591663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2867075852958571881727775 4300613779437857822591663)
          ·
            refine ⟨6450920669156786733887495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4300613779437857822591663 6450920669156786733887495)
            ·
              refine ⟨9676381003735180100831243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6450920669156786733887495 9676381003735180100831243)
              ·
                refine ⟨14514571505602770151246865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9676381003735180100831243 14514571505602770151246865)
                ·
                  refine ⟨10885928629202077613435149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14514571505602770151246865 10885928629202077613435149)
                  ·
                    refine ⟨4082223235950779105038181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10885928629202077613435149 4082223235950779105038181)
                    ·
                      refine ⟨765416856740771082194659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4082223235950779105038181 765416856740771082194659)
                      ·
                        rfl

theorem cell23_1490644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_1490644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1490644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1490644 prefixEnd_1490644 := by exact prefixLift 1490644
  have htrace : WordTrace (prefixWord ++ tailWord_1490644) baseStart_1490644 baseEnd_1490644 := by
    simpa [prefixWord, tailWord_1490644, baseEnd_1490644] using wordTrace_append hprefix tailTrace_1490644
  have hstable : (prefixWord ++ tailWord_1490644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490644).length < 2 ^ (prefixWord ++ tailWord_1490644).sum := by decide
  have hdescent : baseEnd_1490644 < baseStart_1490644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490647 : List Nat := [1, 1, 3, 2, 1, 3, 1, 1, 1, 6, 3]
def baseStart_1490647 : Nat := 118140960795 + 1490647 * 2 ^ 59
def prefixEnd_1490647 : Nat := 4983230072969 + 3 ^ 40 * 1490647 * 2
def baseEnd_1490647 : Nat := 765418397182734570457145

theorem tailTrace_1490647 : CollatzResearch.WordTrace tailWord_1490647 prefixEnd_1490647 765418397182734570457145 := by
  unfold tailWord_1490647
  simp only [CollatzResearch.WordTrace]
  refine ⟨54368362630647976084382195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36245575087098650722921463 54368362630647976084382195)
  ·
    refine ⟨81552543945971964126573293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54368362630647976084382195 81552543945971964126573293)
    ·
      refine ⟨30582203979739486547464985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81552543945971964126573293 30582203979739486547464985)
      ·
        refine ⟨22936652984804614910598739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30582203979739486547464985 22936652984804614910598739)
        ·
          refine ⟨34404979477206922365898109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22936652984804614910598739 34404979477206922365898109)
          ·
            refine ⟨12901867303952595887211791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34404979477206922365898109 12901867303952595887211791)
            ·
              refine ⟨19352800955928893830817687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12901867303952595887211791 19352800955928893830817687)
              ·
                refine ⟨29029201433893340746226531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19352800955928893830817687 29029201433893340746226531)
                ·
                  refine ⟨43543802150840011119339797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29029201433893340746226531 43543802150840011119339797)
                  ·
                    refine ⟨2041115725820625521219053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 43543802150840011119339797 2041115725820625521219053)
                    ·
                      refine ⟨765418397182734570457145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2041115725820625521219053 765418397182734570457145)
                      ·
                        rfl

theorem cell23_1490647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 6, 3].length) (baseStart_1490647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1490647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1490647 prefixEnd_1490647 := by exact prefixLift 1490647
  have htrace : WordTrace (prefixWord ++ tailWord_1490647) baseStart_1490647 baseEnd_1490647 := by
    simpa [prefixWord, tailWord_1490647, baseEnd_1490647] using wordTrace_append hprefix tailTrace_1490647
  have hstable : (prefixWord ++ tailWord_1490647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490647).length < 2 ^ (prefixWord ++ tailWord_1490647).sum := by decide
  have hdescent : baseEnd_1490647 < baseStart_1490647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490661 : List Nat := [1, 3, 1, 4, 1, 1, 4, 1, 1, 4, 2]
def baseStart_1490661 : Nat := 118140960795 + 1490661 * 2 ^ 59
def prefixEnd_1490661 : Nat := 4983230072969 + 3 ^ 40 * 1490661 * 2
def baseEnd_1490661 : Nat := 765425585911897515682081

theorem tailTrace_1490661 : CollatzResearch.WordTrace tailWord_1490661 prefixEnd_1490661 765425585911897515682081 := by
  unfold tailWord_1490661
  simp only [CollatzResearch.WordTrace]
  refine ⟨54368873252597256475391837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36245915501731504316927891 54368873252597256475391837)
  ·
    refine ⟨20388327469723971178271939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54368873252597256475391837 20388327469723971178271939)
    ·
      refine ⟨30582491204585956767407909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20388327469723971178271939 30582491204585956767407909)
      ·
        refine ⟨5734217100859866893888983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30582491204585956767407909 5734217100859866893888983)
        ·
          refine ⟨8601325651289800340833475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5734217100859866893888983 8601325651289800340833475)
          ·
            refine ⟨12901988476934700511250213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8601325651289800340833475 12901988476934700511250213)
            ·
              refine ⟨2419122839425256345859415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12901988476934700511250213 2419122839425256345859415)
              ·
                refine ⟨3628684259137884518789123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2419122839425256345859415 3628684259137884518789123)
                ·
                  refine ⟨5443026388706826778183685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3628684259137884518789123 5443026388706826778183685)
                  ·
                    refine ⟨1020567447882530020909441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5443026388706826778183685 1020567447882530020909441)
                    ·
                      refine ⟨765425585911897515682081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1020567447882530020909441 765425585911897515682081)
                      ·
                        rfl

theorem cell23_1490661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_1490661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1490661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1490661 prefixEnd_1490661 := by exact prefixLift 1490661
  have htrace : WordTrace (prefixWord ++ tailWord_1490661) baseStart_1490661 baseEnd_1490661 := by
    simpa [prefixWord, tailWord_1490661, baseEnd_1490661] using wordTrace_append hprefix tailTrace_1490661
  have hstable : (prefixWord ++ tailWord_1490661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490661).length < 2 ^ (prefixWord ++ tailWord_1490661).sum := by decide
  have hdescent : baseEnd_1490661 < baseStart_1490661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490697 : List Nat := [1, 2, 1, 1, 3, 2, 1, 3, 4, 5]
def baseStart_1490697 : Nat := 118140960795 + 1490697 * 2 ^ 59
def prefixEnd_1490697 : Nat := 4983230072969 + 3 ^ 40 * 1490697 * 2
def baseEnd_1490697 : Nat := 255148023738486458277305

theorem tailTrace_1490697 : CollatzResearch.WordTrace tailWord_1490697 prefixEnd_1490697 255148023738486458277305 := by
  unfold tailWord_1490697
  simp only [CollatzResearch.WordTrace]
  refine ⟨54370186280466834623702345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36246790853644556415801563 54370186280466834623702345)
  ·
    refine ⟨40777639710350125967776759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54370186280466834623702345 40777639710350125967776759)
    ·
      refine ⟨61166459565525188951665139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40777639710350125967776759 61166459565525188951665139)
      ·
        refine ⟨91749689348287783427497709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61166459565525188951665139 91749689348287783427497709)
        ·
          refine ⟨34406133505607918785311641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91749689348287783427497709 34406133505607918785311641)
          ·
            refine ⟨25804600129205939088983731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34406133505607918785311641 25804600129205939088983731)
            ·
              refine ⟨38706900193808908633475597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25804600129205939088983731 38706900193808908633475597)
              ·
                refine ⟨14515087572678340737553349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38706900193808908633475597 14515087572678340737553349)
                ·
                  refine ⟨2721578919877188888291253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14515087572678340737553349 2721578919877188888291253)
                  ·
                    refine ⟨255148023738486458277305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2721578919877188888291253 255148023738486458277305)
                    ·
                      rfl

theorem cell23_1490697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 4, 5].length) (baseStart_1490697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1490697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1490697 prefixEnd_1490697 := by exact prefixLift 1490697
  have htrace : WordTrace (prefixWord ++ tailWord_1490697) baseStart_1490697 baseEnd_1490697 := by
    simpa [prefixWord, tailWord_1490697, baseEnd_1490697] using wordTrace_append hprefix tailTrace_1490697
  have hstable : (prefixWord ++ tailWord_1490697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490697).length < 2 ^ (prefixWord ++ tailWord_1490697).sum := by decide
  have hdescent : baseEnd_1490697 < baseStart_1490697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490751 : List Nat := [1, 1, 2, 2, 6, 1, 1, 2, 2, 1, 4]
def baseStart_1490751 : Nat := 118140960795 + 1490751 * 2 ^ 59
def prefixEnd_1490751 : Nat := 4983230072969 + 3 ^ 40 * 1490751 * 2
def baseEnd_1490751 : Nat := 765471799170802163556667

theorem tailTrace_1490751 : CollatzResearch.WordTrace tailWord_1490751 prefixEnd_1490751 765471799170802163556667 := by
  unfold tailWord_1490751
  simp only [CollatzResearch.WordTrace]
  refine ⟨54372155822271201846168107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36248103881514134564112071 54372155822271201846168107)
  ·
    refine ⟨81558233733406802769252161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54372155822271201846168107 81558233733406802769252161)
    ·
      refine ⟨61168675300055102076939121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81558233733406802769252161 61168675300055102076939121)
      ·
        refine ⟨45876506475041326557704341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61168675300055102076939121 45876506475041326557704341)
        ·
          refine ⟨2150461241017562182392391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 45876506475041326557704341 2150461241017562182392391)
          ·
            refine ⟨3225691861526343273588587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2150461241017562182392391 3225691861526343273588587)
            ·
              refine ⟨4838537792289514910382881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3225691861526343273588587 4838537792289514910382881)
              ·
                refine ⟨3628903344217136182787161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4838537792289514910382881 3628903344217136182787161)
                ·
                  refine ⟨2721677508162852137090371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3628903344217136182787161 2721677508162852137090371)
                  ·
                    refine ⟨4082516262244278205635557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2721677508162852137090371 4082516262244278205635557)
                    ·
                      refine ⟨765471799170802163556667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4082516262244278205635557 765471799170802163556667)
                      ·
                        rfl

theorem cell23_1490751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 2, 2, 1, 4].length) (baseStart_1490751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1490751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1490751 prefixEnd_1490751 := by exact prefixLift 1490751
  have htrace : WordTrace (prefixWord ++ tailWord_1490751) baseStart_1490751 baseEnd_1490751 := by
    simpa [prefixWord, tailWord_1490751, baseEnd_1490751] using wordTrace_append hprefix tailTrace_1490751
  have hstable : (prefixWord ++ tailWord_1490751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490751).length < 2 ^ (prefixWord ++ tailWord_1490751).sum := by decide
  have hdescent : baseEnd_1490751 < baseStart_1490751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490757 : List Nat := [1, 3, 1, 1, 1, 2, 3, 3, 8]
def baseStart_1490757 : Nat := 118140960795 + 1490757 * 2 ^ 59
def prefixEnd_1490757 : Nat := 4983230072969 + 3 ^ 40 * 1490757 * 2
def baseEnd_1490757 : Nat := 85052764450525460009071

theorem tailTrace_1490757 : CollatzResearch.WordTrace tailWord_1490757 prefixEnd_1490757 85052764450525460009071 := by
  unfold tailWord_1490757
  simp only [CollatzResearch.WordTrace]
  refine ⟨54372374660249464870886525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36248249773499643247257683 54372374660249464870886525)
  ·
    refine ⟨20389640497593549326582447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54372374660249464870886525 20389640497593549326582447)
    ·
      refine ⟨30584460746390323989873671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20389640497593549326582447 30584460746390323989873671)
      ·
        refine ⟨45876691119585485984810507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30584460746390323989873671 45876691119585485984810507)
        ·
          refine ⟨68815036679378228977215761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45876691119585485984810507 68815036679378228977215761)
          ·
            refine ⟨51611277509533671732911821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68815036679378228977215761 51611277509533671732911821)
            ·
              refine ⟨19354229066075126899841933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51611277509533671732911821 19354229066075126899841933)
              ·
                refine ⟨7257835899778172587440725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19354229066075126899841933 7257835899778172587440725)
                ·
                  refine ⟨85052764450525460009071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7257835899778172587440725 85052764450525460009071)
                  ·
                    rfl

theorem cell23_1490757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 8].length) (baseStart_1490757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1490757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1490757 prefixEnd_1490757 := by exact prefixLift 1490757
  have htrace : WordTrace (prefixWord ++ tailWord_1490757) baseStart_1490757 baseEnd_1490757 := by
    simpa [prefixWord, tailWord_1490757, baseEnd_1490757] using wordTrace_append hprefix tailTrace_1490757
  have hstable : (prefixWord ++ tailWord_1490757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490757).length < 2 ^ (prefixWord ++ tailWord_1490757).sum := by decide
  have hdescent : baseEnd_1490757 < baseStart_1490757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490758 : List Nat := [6, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5]
def baseStart_1490758 : Nat := 118140960795 + 1490758 * 2 ^ 59
def prefixEnd_1490758 : Nat := 4983230072969 + 3 ^ 40 * 1490758 * 2
def baseEnd_1490758 : Nat := 765475393535383636169135

theorem tailTrace_1490758 : CollatzResearch.WordTrace tailWord_1490758 prefixEnd_1490758 765475393535383636169135 := by
  unfold tailWord_1490758
  simp only [CollatzResearch.WordTrace]
  refine ⟨1699137847913932563802279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 36248274088830561361115285 1699137847913932563802279)
  ·
    refine ⟨2548706771870898845703419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1699137847913932563802279 2548706771870898845703419)
    ·
      refine ⟨3823060157806348268555129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2548706771870898845703419 3823060157806348268555129)
      ·
        refine ⟨2867295118354761201416347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3823060157806348268555129 2867295118354761201416347)
        ·
          refine ⟨4300942677532141802124521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2867295118354761201416347 4300942677532141802124521)
          ·
            refine ⟨3225707008149106351593391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4300942677532141802124521 3225707008149106351593391)
            ·
              refine ⟨4838560512223659527390087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3225707008149106351593391 4838560512223659527390087)
              ·
                refine ⟨7257840768335489291085131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4838560512223659527390087 7257840768335489291085131)
                ·
                  refine ⟨10886761152503233936627697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7257840768335489291085131 10886761152503233936627697)
                  ·
                    refine ⟨8165070864377425452470773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10886761152503233936627697 8165070864377425452470773)
                    ·
                      refine ⟨765475393535383636169135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8165070864377425452470773 765475393535383636169135)
                      ·
                        rfl

theorem cell23_1490758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_1490758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1490758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1490758 prefixEnd_1490758 := by exact prefixLift 1490758
  have htrace : WordTrace (prefixWord ++ tailWord_1490758) baseStart_1490758 baseEnd_1490758 := by
    simpa [prefixWord, tailWord_1490758, baseEnd_1490758] using wordTrace_append hprefix tailTrace_1490758
  have hstable : (prefixWord ++ tailWord_1490758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490758).length < 2 ^ (prefixWord ++ tailWord_1490758).sum := by decide
  have hdescent : baseEnd_1490758 < baseStart_1490758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490788 : List Nat := [2, 3, 1, 1, 5, 1, 2, 1, 2, 2, 3]
def baseStart_1490788 : Nat := 118140960795 + 1490788 * 2 ^ 59
def prefixEnd_1490788 : Nat := 4983230072969 + 3 ^ 40 * 1490788 * 2
def baseEnd_1490788 : Nat := 765490797955018518793997

theorem tailTrace_1490788 : CollatzResearch.WordTrace tailWord_1490788 prefixEnd_1490788 765490797955018518793997 := by
  unfold tailWord_1490788
  simp only [CollatzResearch.WordTrace]
  refine ⟨27186752661568578582632509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36249003548758104776843345 27186752661568578582632509)
  ·
    refine ⟨10195032248088216968487191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27186752661568578582632509 10195032248088216968487191)
    ·
      refine ⟨15292548372132325452730787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10195032248088216968487191 15292548372132325452730787)
      ·
        refine ⟨22938822558198488179096181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15292548372132325452730787 22938822558198488179096181)
        ·
          refine ⟨2150514614831108266790267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22938822558198488179096181 2150514614831108266790267)
          ·
            refine ⟨3225771922246662400185401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2150514614831108266790267 3225771922246662400185401)
            ·
              refine ⟨2419328941684996800139051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3225771922246662400185401 2419328941684996800139051)
              ·
                refine ⟨3628993412527495200208577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2419328941684996800139051 3628993412527495200208577)
                ·
                  refine ⟨2721745059395621400156433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3628993412527495200208577 2721745059395621400156433)
                  ·
                    refine ⟨2041308794546716050117325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2721745059395621400156433 2041308794546716050117325)
                    ·
                      refine ⟨765490797955018518793997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2041308794546716050117325 765490797955018518793997)
                      ·
                        rfl

theorem cell23_1490788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 1, 2, 2, 3].length) (baseStart_1490788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1490788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1490788 prefixEnd_1490788 := by exact prefixLift 1490788
  have htrace : WordTrace (prefixWord ++ tailWord_1490788) baseStart_1490788 baseEnd_1490788 := by
    simpa [prefixWord, tailWord_1490788, baseEnd_1490788] using wordTrace_append hprefix tailTrace_1490788
  have hstable : (prefixWord ++ tailWord_1490788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490788).length < 2 ^ (prefixWord ++ tailWord_1490788).sum := by decide
  have hdescent : baseEnd_1490788 < baseStart_1490788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490845 : List Nat := [1, 4, 2, 1, 2, 4, 1, 1, 2, 3, 2]
def baseStart_1490845 : Nat := 118140960795 + 1490845 * 2 ^ 59
def prefixEnd_1490845 : Nat := 4983230072969 + 3 ^ 40 * 1490845 * 2
def baseEnd_1490845 : Nat := 765520066352324795781235

theorem tailTrace_1490845 : CollatzResearch.WordTrace tailWord_1490845 prefixEnd_1490845 765520066352324795781235 := by
  unfold tailWord_1490845
  simp only [CollatzResearch.WordTrace]
  refine ⟨54375584283930655900089989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36250389522620437266726659 54375584283930655900089989)
  ·
    refine ⟨10195422053236997981266873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54375584283930655900089989 10195422053236997981266873)
    ·
      refine ⟨7646566539927748485950155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10195422053236997981266873 7646566539927748485950155)
      ·
        refine ⟨11469849809891622728925233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7646566539927748485950155 11469849809891622728925233)
        ·
          refine ⟨8602387357418717046693925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11469849809891622728925233 8602387357418717046693925)
          ·
            refine ⟨1612947629516009446255111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8602387357418717046693925 1612947629516009446255111)
            ·
              refine ⟨2419421444274014169382667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1612947629516009446255111 2419421444274014169382667)
              ·
                refine ⟨3629132166411021254074001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2419421444274014169382667 3629132166411021254074001)
                ·
                  refine ⟨2721849124808265940555501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3629132166411021254074001 2721849124808265940555501)
                  ·
                    refine ⟨1020693421803099727708313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2721849124808265940555501 1020693421803099727708313)
                    ·
                      refine ⟨765520066352324795781235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1020693421803099727708313 765520066352324795781235)
                      ·
                        rfl

theorem cell23_1490845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 1, 2, 3, 2].length) (baseStart_1490845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1490845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1490845 prefixEnd_1490845 := by exact prefixLift 1490845
  have htrace : WordTrace (prefixWord ++ tailWord_1490845) baseStart_1490845 baseEnd_1490845 := by
    simpa [prefixWord, tailWord_1490845, baseEnd_1490845] using wordTrace_append hprefix tailTrace_1490845
  have hstable : (prefixWord ++ tailWord_1490845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490845).length < 2 ^ (prefixWord ++ tailWord_1490845).sum := by decide
  have hdescent : baseEnd_1490845 < baseStart_1490845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490855 : List Nat := [1, 1, 6, 1, 2, 3, 2, 1, 1, 5]
def baseStart_1490855 : Nat := 118140960795 + 1490855 * 2 ^ 59
def prefixEnd_1490855 : Nat := 4983230072969 + 3 ^ 40 * 1490855 * 2
def baseEnd_1490855 : Nat := 255175067052956585552063

theorem tailTrace_1490855 : CollatzResearch.WordTrace tailWord_1490855 prefixEnd_1490855 255175067052956585552063 := by
  unfold tailWord_1490855
  simp only [CollatzResearch.WordTrace]
  refine ⟨54375949013894427607954019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36250632675929618405302679 54375949013894427607954019)
  ·
    refine ⟨81563923520841641411931029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54375949013894427607954019 81563923520841641411931029)
    ·
      refine ⟨3823308915039451941184267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 81563923520841641411931029 3823308915039451941184267)
      ·
        refine ⟨5734963372559177911776401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3823308915039451941184267 5734963372559177911776401)
        ·
          refine ⟨4301222529419383433832301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5734963372559177911776401 4301222529419383433832301)
          ·
            refine ⟨1612958448532268787687113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4301222529419383433832301 1612958448532268787687113)
            ·
              refine ⟨1209718836399201590765335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1612958448532268787687113 1209718836399201590765335)
              ·
                refine ⟨1814578254598802386148003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1209718836399201590765335 1814578254598802386148003)
                ·
                  refine ⟨2721867381898203579222005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1814578254598802386148003 2721867381898203579222005)
                  ·
                    refine ⟨255175067052956585552063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2721867381898203579222005 255175067052956585552063)
                    ·
                      rfl

theorem cell23_1490855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_1490855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1490855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1490855 prefixEnd_1490855 := by exact prefixLift 1490855
  have htrace : WordTrace (prefixWord ++ tailWord_1490855) baseStart_1490855 baseEnd_1490855 := by
    simpa [prefixWord, tailWord_1490855, baseEnd_1490855] using wordTrace_append hprefix tailTrace_1490855
  have hstable : (prefixWord ++ tailWord_1490855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490855).length < 2 ^ (prefixWord ++ tailWord_1490855).sum := by decide
  have hdescent : baseEnd_1490855 < baseStart_1490855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490888 : List Nat := [2, 1, 3, 1, 4, 3, 1, 1, 1, 2, 4]
def baseStart_1490888 : Nat := 118140960795 + 1490888 * 2 ^ 59
def prefixEnd_1490888 : Nat := 4983230072969 + 3 ^ 40 * 1490888 * 2
def baseEnd_1490888 : Nat := 765542146020468127543537

theorem tailTrace_1490888 : CollatzResearch.WordTrace tailWord_1490888 prefixEnd_1490888 765542146020468127543537 := by
  unfold tailWord_1490888
  simp only [CollatzResearch.WordTrace]
  refine ⟨27188576311387437121952659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36251435081849916162603545 27188576311387437121952659)
  ·
    refine ⟨40782864467081155682928989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27188576311387437121952659 40782864467081155682928989)
    ·
      refine ⟨15293574175155433381098371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40782864467081155682928989 15293574175155433381098371)
      ·
        refine ⟨22940361262733150071647557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15293574175155433381098371 22940361262733150071647557)
        ·
          refine ⟨4301317736762465638433917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22940361262733150071647557 4301317736762465638433917)
          ·
            refine ⟨1612994151285924614412719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4301317736762465638433917 1612994151285924614412719)
            ·
              refine ⟨2419491226928886921619079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1612994151285924614412719 2419491226928886921619079)
              ·
                refine ⟨3629236840393330382428619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2419491226928886921619079 3629236840393330382428619)
                ·
                  refine ⟨5443855260589995573642929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3629236840393330382428619 5443855260589995573642929)
                  ·
                    refine ⟨4082891445442496680232197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5443855260589995573642929 4082891445442496680232197)
                    ·
                      refine ⟨765542146020468127543537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4082891445442496680232197 765542146020468127543537)
                      ·
                        rfl

theorem cell23_1490888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 1, 1, 2, 4].length) (baseStart_1490888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1490888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1490888 prefixEnd_1490888 := by exact prefixLift 1490888
  have htrace : WordTrace (prefixWord ++ tailWord_1490888) baseStart_1490888 baseEnd_1490888 := by
    simpa [prefixWord, tailWord_1490888, baseEnd_1490888] using wordTrace_append hprefix tailTrace_1490888
  have hstable : (prefixWord ++ tailWord_1490888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490888).length < 2 ^ (prefixWord ++ tailWord_1490888).sum := by decide
  have hdescent : baseEnd_1490888 < baseStart_1490888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490904 : List Nat := [2, 1, 2, 2, 2, 2, 1, 1, 1, 4, 5]
def baseStart_1490904 : Nat := 118140960795 + 1490904 * 2 ^ 59
def prefixEnd_1490904 : Nat := 4983230072969 + 3 ^ 40 * 1490904 * 2
def baseEnd_1490904 : Nat := 765550361710940064943463

theorem tailTrace_1490904 : CollatzResearch.WordTrace tailWord_1490904 prefixEnd_1490904 765550361710940064943463 := by
  unfold tailWord_1490904
  simp only [CollatzResearch.WordTrace]
  refine ⟨27188868095358454488243883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36251824127144605984325177 27188868095358454488243883)
  ·
    refine ⟨40783302143037681732365825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27188868095358454488243883 40783302143037681732365825)
    ·
      refine ⟨30587476607278261299274369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40783302143037681732365825 30587476607278261299274369)
      ·
        refine ⟨22940607455458695974455777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30587476607278261299274369 22940607455458695974455777)
        ·
          refine ⟨17205455591594021980841833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22940607455458695974455777 17205455591594021980841833)
          ·
            refine ⟨12904091693695516485631375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17205455591594021980841833 12904091693695516485631375)
            ·
              refine ⟨19356137540543274728447063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12904091693695516485631375 19356137540543274728447063)
              ·
                refine ⟨29034206310814912092670595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19356137540543274728447063 29034206310814912092670595)
                ·
                  refine ⟨43551309466222368139005893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29034206310814912092670595 43551309466222368139005893)
                  ·
                    refine ⟨8165870524916694026063605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43551309466222368139005893 8165870524916694026063605)
                    ·
                      refine ⟨765550361710940064943463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8165870524916694026063605 765550361710940064943463)
                      ·
                        rfl

theorem cell23_1490904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_1490904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1490904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1490904 prefixEnd_1490904 := by exact prefixLift 1490904
  have htrace : WordTrace (prefixWord ++ tailWord_1490904) baseStart_1490904 baseEnd_1490904 := by
    simpa [prefixWord, tailWord_1490904, baseEnd_1490904] using wordTrace_append hprefix tailTrace_1490904
  have hstable : (prefixWord ++ tailWord_1490904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490904).length < 2 ^ (prefixWord ++ tailWord_1490904).sum := by decide
  have hdescent : baseEnd_1490904 < baseStart_1490904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490924 : List Nat := [2, 2, 1, 1, 2, 1, 1, 3, 4, 6]
def baseStart_1490924 : Nat := 118140960795 + 1490924 * 2 ^ 59
def prefixEnd_1490924 : Nat := 4983230072969 + 3 ^ 40 * 1490924 * 2
def baseEnd_1490924 : Nat := 255186877108009995564457

theorem tailTrace_1490924 : CollatzResearch.WordTrace tailWord_1490924 prefixEnd_1490924 255186877108009995564457 := by
  unfold tailWord_1490924
  simp only [CollatzResearch.WordTrace]
  refine ⟨27189232825322226196107913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36252310433762968261477217 27189232825322226196107913)
  ·
    refine ⟨20391924618991669647080935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27189232825322226196107913 20391924618991669647080935)
    ·
      refine ⟨30587886928487504470621403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20391924618991669647080935 30587886928487504470621403)
      ·
        refine ⟨45881830392731256705932105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30587886928487504470621403 45881830392731256705932105)
        ·
          refine ⟨34411372794548442529449079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45881830392731256705932105 34411372794548442529449079)
          ·
            refine ⟨51617059191822663794173619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34411372794548442529449079 51617059191822663794173619)
            ·
              refine ⟨77425588787733995691260429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51617059191822663794173619 77425588787733995691260429)
              ·
                refine ⟨29034595795400248384222661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77425588787733995691260429 29034595795400248384222661)
                ·
                  refine ⟨5443986711637546572041749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29034595795400248384222661 5443986711637546572041749)
                  ·
                    refine ⟨255186877108009995564457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5443986711637546572041749 255186877108009995564457)
                    ·
                      rfl

theorem cell23_1490924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 6].length) (baseStart_1490924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1490924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1490924 prefixEnd_1490924 := by exact prefixLift 1490924
  have htrace : WordTrace (prefixWord ++ tailWord_1490924) baseStart_1490924 baseEnd_1490924 := by
    simpa [prefixWord, tailWord_1490924, baseEnd_1490924] using wordTrace_append hprefix tailTrace_1490924
  have hstable : (prefixWord ++ tailWord_1490924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490924).length < 2 ^ (prefixWord ++ tailWord_1490924).sum := by decide
  have hdescent : baseEnd_1490924 < baseStart_1490924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490942 : List Nat := [4, 2, 2, 2, 1, 2, 1, 3, 2, 1, 3]
def baseStart_1490942 : Nat := 118140960795 + 1490942 * 2 ^ 59
def prefixEnd_1490942 : Nat := 4983230072969 + 3 ^ 40 * 1490942 * 2
def baseEnd_1490942 : Nat := 765569873975810916268289

theorem tailTrace_1490942 : CollatzResearch.WordTrace tailWord_1490942 prefixEnd_1490942 765569873975810916268289 := by
  unfold tailWord_1490942
  simp only [CollatzResearch.WordTrace]
  refine ⟨6797390270572405183296385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36252748109719494310914053 6797390270572405183296385)
  ·
    refine ⟨5098042702929303887472289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6797390270572405183296385 5098042702929303887472289)
    ·
      refine ⟨3823532027196977915604217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5098042702929303887472289 3823532027196977915604217)
      ·
        refine ⟨2867649020397733436703163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3823532027196977915604217 2867649020397733436703163)
        ·
          refine ⟨4301473530596600155054745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2867649020397733436703163 4301473530596600155054745)
          ·
            refine ⟨3226105147947450116291059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4301473530596600155054745 3226105147947450116291059)
            ·
              refine ⟨4839157721921175174436589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3226105147947450116291059 4839157721921175174436589)
              ·
                refine ⟨1814684145720440690413721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4839157721921175174436589 1814684145720440690413721)
                ·
                  refine ⟨1361013109290330517810291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1814684145720440690413721 1361013109290330517810291)
                  ·
                    refine ⟨2041519663935495776715437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1361013109290330517810291 2041519663935495776715437)
                    ·
                      refine ⟨765569873975810916268289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2041519663935495776715437 765569873975810916268289)
                      ·
                        rfl

theorem cell23_1490942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_1490942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1490942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1490942 prefixEnd_1490942 := by exact prefixLift 1490942
  have htrace : WordTrace (prefixWord ++ tailWord_1490942) baseStart_1490942 baseEnd_1490942 := by
    simpa [prefixWord, tailWord_1490942, baseEnd_1490942] using wordTrace_append hprefix tailTrace_1490942
  have hstable : (prefixWord ++ tailWord_1490942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490942).length < 2 ^ (prefixWord ++ tailWord_1490942).sum := by decide
  have hdescent : baseEnd_1490942 < baseStart_1490942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
