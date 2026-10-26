import V185TrunkScan23Chunk0961

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5695839 : List Nat := [1, 1, 2, 3, 1, 2, 2, 2, 1, 5, 3]
def baseStart_5695839 : Nat := 118140960795 + 5695839 * 2 ^ 59
def prefixEnd_5695839 : Nat := 4983230072969 + 3 ^ 40 * 5695839 * 2
def baseEnd_5695839 : Nat := 2924703137624445737417819

theorem tailTrace_5695839 : CollatzResearch.WordTrace tailWord_5695839 prefixEnd_5695839 2924703137624445737417819 := by
  unfold tailWord_5695839
  simp only [CollatzResearch.WordTrace]
  refine ⟨207744315211955549699986571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138496210141303699799991047 207744315211955549699986571)
  ·
    refine ⟨311616472817933324549979857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207744315211955549699986571 311616472817933324549979857)
    ·
      refine ⟨233712354613449993412484893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311616472817933324549979857 233712354613449993412484893)
      ·
        refine ⟨87642132980043747529681835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 233712354613449993412484893 87642132980043747529681835)
        ·
          refine ⟨131463199470065621294522753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87642132980043747529681835 131463199470065621294522753)
          ·
            refine ⟨98597399602549215970892065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131463199470065621294522753 98597399602549215970892065)
            ·
              refine ⟨73948049701911911978169049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98597399602549215970892065 73948049701911911978169049)
              ·
                refine ⟨55461037276433933983626787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73948049701911911978169049 55461037276433933983626787)
                ·
                  refine ⟨83191555914650900975440181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55461037276433933983626787 83191555914650900975440181)
                  ·
                    refine ⟨7799208366998521966447517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 83191555914650900975440181 7799208366998521966447517)
                    ·
                      refine ⟨2924703137624445737417819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7799208366998521966447517 2924703137624445737417819)
                      ·
                        rfl

theorem cell23_5695839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 5, 3].length) (baseStart_5695839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5695839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5695839 prefixEnd_5695839 := by exact prefixLift 5695839
  have htrace : WordTrace (prefixWord ++ tailWord_5695839) baseStart_5695839 baseEnd_5695839 := by
    simpa [prefixWord, tailWord_5695839, baseEnd_5695839] using wordTrace_append hprefix tailTrace_5695839
  have hstable : (prefixWord ++ tailWord_5695839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5695839).length < 2 ^ (prefixWord ++ tailWord_5695839).sum := by decide
  have hdescent : baseEnd_5695839 < baseStart_5695839 := by decide
  rcases family_descends (prefixWord ++ tailWord_5695839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5695859 : List Nat := [1, 1, 1, 2, 2, 1, 2, 6, 2, 5]
def baseStart_5695859 : Nat := 118140960795 + 5695859 * 2 ^ 59
def prefixEnd_5695859 : Nat := 4983230072969 + 3 ^ 40 * 5695859 * 2
def baseEnd_5695859 : Nat := 974904469079178553055909

theorem tailTrace_5695859 : CollatzResearch.WordTrace tailWord_5695859 prefixEnd_5695859 974904469079178553055909 := by
  unfold tailWord_5695859
  simp only [CollatzResearch.WordTrace]
  refine ⟨207745044671883093115714631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138496696447922062077143087 207745044671883093115714631)
  ·
    refine ⟨311617567007824639673571947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207745044671883093115714631 311617567007824639673571947)
    ·
      refine ⟨467426350511736959510357921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311617567007824639673571947 467426350511736959510357921)
      ·
        refine ⟨350569762883802719632768441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 467426350511736959510357921 350569762883802719632768441)
        ·
          refine ⟨262927322162852039724576331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 350569762883802719632768441 262927322162852039724576331)
          ·
            refine ⟨394390983244278059586864497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262927322162852039724576331 394390983244278059586864497)
            ·
              refine ⟨295793237433208544690148373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 394390983244278059586864497 295793237433208544690148373)
              ·
                refine ⟨13865308004681650532350705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 295793237433208544690148373 13865308004681650532350705)
                ·
                  refine ⟨10398981003511237899263029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13865308004681650532350705 10398981003511237899263029)
                  ·
                    refine ⟨974904469079178553055909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10398981003511237899263029 974904469079178553055909)
                    ·
                      rfl

theorem cell23_5695859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6, 2, 5].length) (baseStart_5695859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5695859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5695859 prefixEnd_5695859 := by exact prefixLift 5695859
  have htrace : WordTrace (prefixWord ++ tailWord_5695859) baseStart_5695859 baseEnd_5695859 := by
    simpa [prefixWord, tailWord_5695859, baseEnd_5695859] using wordTrace_append hprefix tailTrace_5695859
  have hstable : (prefixWord ++ tailWord_5695859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5695859).length < 2 ^ (prefixWord ++ tailWord_5695859).sum := by decide
  have hdescent : baseEnd_5695859 < baseStart_5695859 := by decide
  rcases family_descends (prefixWord ++ tailWord_5695859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5695869 : List Nat := [1, 4, 1, 1, 2, 3, 1, 1, 1, 1, 7]
def baseStart_5695869 : Nat := 118140960795 + 5695869 * 2 ^ 59
def prefixEnd_5695869 : Nat := 4983230072969 + 3 ^ 40 * 5695869 * 2
def baseEnd_5695869 : Nat := 2924718542044080620042681

theorem tailTrace_5695869 : CollatzResearch.WordTrace tailWord_5695869 prefixEnd_5695869 2924718542044080620042681 := by
  unfold tailWord_5695869
  simp only [CollatzResearch.WordTrace]
  refine ⟨207745409401846864823578661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138496939601231243215719107 207745409401846864823578661)
  ·
    refine ⟨38952264262846287154420999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 207745409401846864823578661 38952264262846287154420999)
    ·
      refine ⟨58428396394269430731631499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38952264262846287154420999 58428396394269430731631499)
      ·
        refine ⟨87642594591404146097447249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58428396394269430731631499 87642594591404146097447249)
        ·
          refine ⟨65731945943553109573085437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87642594591404146097447249 65731945943553109573085437)
          ·
            refine ⟨24649479728832416089907039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65731945943553109573085437 24649479728832416089907039)
            ·
              refine ⟨36974219593248624134860559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24649479728832416089907039 36974219593248624134860559)
              ·
                refine ⟨55461329389872936202290839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36974219593248624134860559 55461329389872936202290839)
                ·
                  refine ⟨83191994084809404303436259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55461329389872936202290839 83191994084809404303436259)
                  ·
                    refine ⟨124787991127214106455154389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 83191994084809404303436259 124787991127214106455154389)
                    ·
                      refine ⟨2924718542044080620042681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 124787991127214106455154389 2924718542044080620042681)
                      ·
                        rfl

theorem cell23_5695869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_5695869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5695869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5695869 prefixEnd_5695869 := by exact prefixLift 5695869
  have htrace : WordTrace (prefixWord ++ tailWord_5695869) baseStart_5695869 baseEnd_5695869 := by
    simpa [prefixWord, tailWord_5695869, baseEnd_5695869] using wordTrace_append hprefix tailTrace_5695869
  have hstable : (prefixWord ++ tailWord_5695869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5695869).length < 2 ^ (prefixWord ++ tailWord_5695869).sum := by decide
  have hdescent : baseEnd_5695869 < baseStart_5695869 := by decide
  rcases family_descends (prefixWord ++ tailWord_5695869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5695874 : List Nat := [3, 4, 2, 1, 2, 1, 1, 3, 2, 2, 2]
def baseStart_5695874 : Nat := 118140960795 + 5695874 * 2 ^ 59
def prefixEnd_5695874 : Nat := 4983230072969 + 3 ^ 40 * 5695874 * 2
def baseEnd_5695874 : Nat := 2924721109447353100480159

theorem tailTrace_5695874 : CollatzResearch.WordTrace tailWord_5695874 prefixEnd_5695874 2924721109447353100480159 := by
  unfold tailWord_5695874
  simp only [CollatzResearch.WordTrace]
  refine ⟨51936397941707187669377669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138497061177885833785007117 51936397941707187669377669)
  ·
    refine ⟨9738074614070097688008313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51936397941707187669377669 9738074614070097688008313)
    ·
      refine ⟨7303555960552573266006235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9738074614070097688008313 7303555960552573266006235)
      ·
        refine ⟨10955333940828859899009353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7303555960552573266006235 10955333940828859899009353)
        ·
          refine ⟨8216500455621644924257015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10955333940828859899009353 8216500455621644924257015)
          ·
            refine ⟨12324750683432467386385523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8216500455621644924257015 12324750683432467386385523)
            ·
              refine ⟨18487126025148701079578285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12324750683432467386385523 18487126025148701079578285)
              ·
                refine ⟨6932672259430762904841857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18487126025148701079578285 6932672259430762904841857)
                ·
                  refine ⟨5199504194573072178631393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6932672259430762904841857 5199504194573072178631393)
                  ·
                    refine ⟨3899628145929804133973545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5199504194573072178631393 3899628145929804133973545)
                    ·
                      refine ⟨2924721109447353100480159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3899628145929804133973545 2924721109447353100480159)
                      ·
                        rfl

theorem cell23_5695874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_5695874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5695874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5695874 prefixEnd_5695874 := by exact prefixLift 5695874
  have htrace : WordTrace (prefixWord ++ tailWord_5695874) baseStart_5695874 baseEnd_5695874 := by
    simpa [prefixWord, tailWord_5695874, baseEnd_5695874] using wordTrace_append hprefix tailTrace_5695874
  have hstable : (prefixWord ++ tailWord_5695874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5695874).length < 2 ^ (prefixWord ++ tailWord_5695874).sum := by decide
  have hdescent : baseEnd_5695874 < baseStart_5695874 := by decide
  rcases family_descends (prefixWord ++ tailWord_5695874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5695909 : List Nat := [1, 3, 1, 2, 1, 1, 4, 1, 2, 1, 6]
def baseStart_5695909 : Nat := 118140960795 + 5695909 * 2 ^ 59
def prefixEnd_5695909 : Nat := 4983230072969 + 3 ^ 40 * 5695909 * 2
def baseEnd_5695909 : Nat := 2924739081270260463542497

theorem tailTrace_5695909 : CollatzResearch.WordTrace tailWord_5695909 prefixEnd_5695909 2924739081270260463542497 := by
  unfold tailWord_5695909
  simp only [CollatzResearch.WordTrace]
  refine ⟨207746868321701951655034781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138497912214467967770023187 207746868321701951655034781)
  ·
    refine ⟨77905075620638231870638043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207746868321701951655034781 77905075620638231870638043)
    ·
      refine ⟨116857613430957347805957065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77905075620638231870638043 116857613430957347805957065)
      ·
        refine ⟨87643210073218010854467799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116857613430957347805957065 87643210073218010854467799)
        ·
          refine ⟨131464815109827016281701699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87643210073218010854467799 131464815109827016281701699)
          ·
            refine ⟨197197222664740524422552549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131464815109827016281701699 197197222664740524422552549)
            ·
              refine ⟨36974479249638848329228603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 197197222664740524422552549 36974479249638848329228603)
              ·
                refine ⟨55461718874458272493842905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36974479249638848329228603 55461718874458272493842905)
                ·
                  refine ⟨41596289155843704370382179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55461718874458272493842905 41596289155843704370382179)
                  ·
                    refine ⟨62394433733765556555573269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41596289155843704370382179 62394433733765556555573269)
                    ·
                      refine ⟨2924739081270260463542497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62394433733765556555573269 2924739081270260463542497)
                      ·
                        rfl

theorem cell23_5695909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_5695909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5695909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5695909 prefixEnd_5695909 := by exact prefixLift 5695909
  have htrace : WordTrace (prefixWord ++ tailWord_5695909) baseStart_5695909 baseEnd_5695909 := by
    simpa [prefixWord, tailWord_5695909, baseEnd_5695909] using wordTrace_append hprefix tailTrace_5695909
  have hstable : (prefixWord ++ tailWord_5695909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5695909).length < 2 ^ (prefixWord ++ tailWord_5695909).sum := by decide
  have hdescent : baseEnd_5695909 < baseStart_5695909 := by decide
  rcases family_descends (prefixWord ++ tailWord_5695909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5695940 : List Nat := [2, 3, 3, 2, 2, 1, 1, 2, 3, 4]
def baseStart_5695940 : Nat := 118140960795 + 5695940 * 2 ^ 59
def prefixEnd_5695940 : Nat := 4983230072969 + 3 ^ 40 * 5695940 * 2
def baseEnd_5695940 : Nat := 974918333056849947418285

theorem tailTrace_5695940 : CollatzResearch.WordTrace tailWord_5695940 prefixEnd_5695940 974918333056849947418285 := by
  unfold tailWord_5695940
  simp only [CollatzResearch.WordTrace]
  refine ⟨103873999492294821974706637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138498665989726429299608849 103873999492294821974706637)
  ·
    refine ⟨38952749809610558240514989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103873999492294821974706637 38952749809610558240514989)
    ·
      refine ⟨14607281178603959340193121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38952749809610558240514989 14607281178603959340193121)
      ·
        refine ⟨10955460883952969505144841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14607281178603959340193121 10955460883952969505144841)
        ·
          refine ⟨8216595662964727128858631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10955460883952969505144841 8216595662964727128858631)
          ·
            refine ⟨12324893494447090693287947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8216595662964727128858631 12324893494447090693287947)
            ·
              refine ⟨18487340241670636039931921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12324893494447090693287947 18487340241670636039931921)
              ·
                refine ⟨13865505181252977029948941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18487340241670636039931921 13865505181252977029948941)
                ·
                  refine ⟨5199564442969866386230853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13865505181252977029948941 5199564442969866386230853)
                  ·
                    refine ⟨974918333056849947418285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5199564442969866386230853 974918333056849947418285)
                    ·
                      rfl

theorem cell23_5695940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_5695940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5695940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5695940 prefixEnd_5695940 := by exact prefixLift 5695940
  have htrace : WordTrace (prefixWord ++ tailWord_5695940) baseStart_5695940 baseEnd_5695940 := by
    simpa [prefixWord, tailWord_5695940, baseEnd_5695940] using wordTrace_append hprefix tailTrace_5695940
  have hstable : (prefixWord ++ tailWord_5695940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5695940).length < 2 ^ (prefixWord ++ tailWord_5695940).sum := by decide
  have hdescent : baseEnd_5695940 < baseStart_5695940 := by decide
  rcases family_descends (prefixWord ++ tailWord_5695940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5695959 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 1, 6, 5]
def baseStart_5695959 : Nat := 118140960795 + 5695959 * 2 ^ 59
def prefixEnd_5695959 : Nat := 4983230072969 + 3 ^ 40 * 5695959 * 2
def baseEnd_5695959 : Nat := 2924764755302985267917267

theorem tailTrace_5695959 : CollatzResearch.WordTrace tailWord_5695959 prefixEnd_5695959 2924764755302985267917267 := by
  unfold tailWord_5695959
  simp only [CollatzResearch.WordTrace]
  refine ⟨207748691971520810194354931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138499127981013873462903287 207748691971520810194354931)
  ·
    refine ⟨311623037957281215291532397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207748691971520810194354931 311623037957281215291532397)
    ·
      refine ⟨116858639233980455734324649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 311623037957281215291532397 116858639233980455734324649)
      ·
        refine ⟨87643979425485341800743487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116858639233980455734324649 87643979425485341800743487)
        ·
          refine ⟨131465969138228012701115231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87643979425485341800743487 131465969138228012701115231)
          ·
            refine ⟨197198953707342019051672847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131465969138228012701115231 197198953707342019051672847)
            ·
              refine ⟨295798430561013028577509271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197198953707342019051672847 295798430561013028577509271)
              ·
                refine ⟨443697645841519542866263907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 295798430561013028577509271 443697645841519542866263907)
                ·
                  refine ⟨665546468762279314299395861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 443697645841519542866263907 665546468762279314299395861)
                  ·
                    refine ⟨31197490723231842857784181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 665546468762279314299395861 31197490723231842857784181)
                    ·
                      refine ⟨2924764755302985267917267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31197490723231842857784181 2924764755302985267917267)
                      ·
                        rfl

theorem cell23_5695959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_5695959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5695959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5695959 prefixEnd_5695959 := by exact prefixLift 5695959
  have htrace : WordTrace (prefixWord ++ tailWord_5695959) baseStart_5695959 baseEnd_5695959 := by
    simpa [prefixWord, tailWord_5695959, baseEnd_5695959] using wordTrace_append hprefix tailTrace_5695959
  have hstable : (prefixWord ++ tailWord_5695959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5695959).length < 2 ^ (prefixWord ++ tailWord_5695959).sum := by decide
  have hdescent : baseEnd_5695959 < baseStart_5695959 := by decide
  rcases family_descends (prefixWord ++ tailWord_5695959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5695970 : List Nat := [3, 3, 3, 2, 1, 1, 1, 1, 8]
def baseStart_5695970 : Nat := 118140960795 + 5695970 * 2 ^ 59
def prefixEnd_5695970 : Nat := 4983230072969 + 3 ^ 40 * 5695970 * 2
def baseEnd_5695970 : Nat := 324974489287798302764413

theorem tailTrace_5695970 : CollatzResearch.WordTrace tailWord_5695970 prefixEnd_5695970 324974489287798302764413 := by
  unfold tailWord_5695970
  simp only [CollatzResearch.WordTrace]
  refine ⟨51937273293620239768251341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138499395449653972715336909 51937273293620239768251341)
  ·
    refine ⟨19476477485107589913094253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51937273293620239768251341 19476477485107589913094253)
    ·
      refine ⟨7303679056915346217410345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19476477485107589913094253 7303679056915346217410345)
      ·
        refine ⟨5477759292686509663057759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7303679056915346217410345 5477759292686509663057759)
        ·
          refine ⟨8216638939029764494586639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5477759292686509663057759 8216638939029764494586639)
          ·
            refine ⟨12324958408544646741879959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8216638939029764494586639 12324958408544646741879959)
            ·
              refine ⟨18487437612816970112819939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12324958408544646741879959 18487437612816970112819939)
              ·
                refine ⟨27731156419225455169229909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18487437612816970112819939 27731156419225455169229909)
                ·
                  refine ⟨324974489287798302764413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27731156419225455169229909 324974489287798302764413)
                  ·
                    rfl

theorem cell23_5695970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 8].length) (baseStart_5695970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5695970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5695970 prefixEnd_5695970 := by exact prefixLift 5695970
  have htrace : WordTrace (prefixWord ++ tailWord_5695970) baseStart_5695970 baseEnd_5695970 := by
    simpa [prefixWord, tailWord_5695970, baseEnd_5695970] using wordTrace_append hprefix tailTrace_5695970
  have hstable : (prefixWord ++ tailWord_5695970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5695970).length < 2 ^ (prefixWord ++ tailWord_5695970).sum := by decide
  have hdescent : baseEnd_5695970 < baseStart_5695970 := by decide
  rcases family_descends (prefixWord ++ tailWord_5695970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5695980 : List Nat := [2, 2, 1, 1, 2, 1, 3, 6, 1, 1, 3]
def baseStart_5695980 : Nat := 118140960795 + 5695980 * 2 ^ 59
def prefixEnd_5695980 : Nat := 4983230072969 + 3 ^ 40 * 5695980 * 2
def baseEnd_5695980 : Nat := 2924775538396729685754671

theorem tailTrace_5695980 : CollatzResearch.WordTrace tailWord_5695980 prefixEnd_5695980 2924775538396729685754671 := by
  unfold tailWord_5695980
  simp only [CollatzResearch.WordTrace]
  refine ⟨103874728952222365390434697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138499638602963153853912929 103874728952222365390434697)
  ·
    refine ⟨77906046714166774042826023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103874728952222365390434697 77906046714166774042826023)
    ·
      refine ⟨116859070071250161064239035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77906046714166774042826023 116859070071250161064239035)
      ·
        refine ⟨175288605106875241596358553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116859070071250161064239035 175288605106875241596358553)
        ·
          refine ⟨131466453830156431197268915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175288605106875241596358553 131466453830156431197268915)
          ·
            refine ⟨197199680745234646795903373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131466453830156431197268915 197199680745234646795903373)
            ·
              refine ⟨73949880279462992548463765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 197199680745234646795903373 73949880279462992548463765)
              ·
                refine ⟨3466400638099827775709239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 73949880279462992548463765 3466400638099827775709239)
                ·
                  refine ⟨5199600957149741663563859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3466400638099827775709239 5199600957149741663563859)
                  ·
                    refine ⟨7799401435724612495345789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5199600957149741663563859 7799401435724612495345789)
                    ·
                      refine ⟨2924775538396729685754671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7799401435724612495345789 2924775538396729685754671)
                      ·
                        rfl

theorem cell23_5695980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 6, 1, 1, 3].length) (baseStart_5695980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5695980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5695980 prefixEnd_5695980 := by exact prefixLift 5695980
  have htrace : WordTrace (prefixWord ++ tailWord_5695980) baseStart_5695980 baseEnd_5695980 := by
    simpa [prefixWord, tailWord_5695980, baseEnd_5695980] using wordTrace_append hprefix tailTrace_5695980
  have hstable : (prefixWord ++ tailWord_5695980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5695980).length < 2 ^ (prefixWord ++ tailWord_5695980).sum := by decide
  have hdescent : baseEnd_5695980 < baseStart_5695980 := by decide
  rcases family_descends (prefixWord ++ tailWord_5695980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5696003 : List Nat := [1, 1, 1, 3, 2, 1, 6, 2, 1, 1, 4]
def baseStart_5696003 : Nat := 118140960795 + 5696003 * 2 ^ 59
def prefixEnd_5696003 : Nat := 4983230072969 + 3 ^ 40 * 5696003 * 2
def baseEnd_5696003 : Nat := 2924787348451783095767065

theorem tailTrace_5696003 : CollatzResearch.WordTrace tailWord_5696003 prefixEnd_5696003 2924787348451783095767065 := by
  unfold tailWord_5696003
  simp only [CollatzResearch.WordTrace]
  refine ⟨207750296783361405708956663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138500197855574270472637775 207750296783361405708956663)
  ·
    refine ⟨311625445175042108563434995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207750296783361405708956663 311625445175042108563434995)
    ·
      refine ⟨467438167762563162845152493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311625445175042108563434995 467438167762563162845152493)
      ·
        refine ⟨175289312910961186066932185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 467438167762563162845152493 175289312910961186066932185)
        ·
          refine ⟨131466984683220889550199139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175289312910961186066932185 131466984683220889550199139)
          ·
            refine ⟨197200477024831334325298709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131466984683220889550199139 197200477024831334325298709)
            ·
              refine ⟨9243772360538968796498377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 197200477024831334325298709 9243772360538968796498377)
              ·
                refine ⟨6932829270404226597373783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9243772360538968796498377 6932829270404226597373783)
                ·
                  refine ⟨10399243905606339896060675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6932829270404226597373783 10399243905606339896060675)
                  ·
                    refine ⟨15598865858409509844091013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10399243905606339896060675 15598865858409509844091013)
                    ·
                      refine ⟨2924787348451783095767065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15598865858409509844091013 2924787348451783095767065)
                      ·
                        rfl

theorem cell23_5696003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 2, 1, 1, 4].length) (baseStart_5696003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5696003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5696003 prefixEnd_5696003 := by exact prefixLift 5696003
  have htrace : WordTrace (prefixWord ++ tailWord_5696003) baseStart_5696003 baseEnd_5696003 := by
    simpa [prefixWord, tailWord_5696003, baseEnd_5696003] using wordTrace_append hprefix tailTrace_5696003
  have hstable : (prefixWord ++ tailWord_5696003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5696003).length < 2 ^ (prefixWord ++ tailWord_5696003).sum := by decide
  have hdescent : baseEnd_5696003 < baseStart_5696003 := by decide
  rcases family_descends (prefixWord ++ tailWord_5696003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5696014 : List Nat := [4, 1, 1, 2, 3, 3, 1, 3, 1, 1, 3]
def baseStart_5696014 : Nat := 118140960795 + 5696014 * 2 ^ 59
def prefixEnd_5696014 : Nat := 4983230072969 + 3 ^ 40 * 5696014 * 2
def baseEnd_5696014 : Nat := 2924792996738982552729515

theorem tailTrace_5696014 : CollatzResearch.WordTrace tailWord_5696014 prefixEnd_5696014 2924792996738982552729515 := by
  unfold tailWord_5696014
  simp only [CollatzResearch.WordTrace]
  refine ⟨25968837248290194323450887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138500465324214369725071397 25968837248290194323450887)
  ·
    refine ⟨38953255872435291485176331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25968837248290194323450887 38953255872435291485176331)
    ·
      refine ⟨58429883808652937227764497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38953255872435291485176331 58429883808652937227764497)
      ·
        refine ⟨43822412856489702920823373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58429883808652937227764497 43822412856489702920823373)
        ·
          refine ⟨16433404821183638595308765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43822412856489702920823373 16433404821183638595308765)
          ·
            refine ⟨6162526807943864473240787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16433404821183638595308765 6162526807943864473240787)
            ·
              refine ⟨9243790211915796709861181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6162526807943864473240787 9243790211915796709861181)
              ·
                refine ⟨3466421329468423766197943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9243790211915796709861181 3466421329468423766197943)
                ·
                  refine ⟨5199631994202635649296915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3466421329468423766197943 5199631994202635649296915)
                  ·
                    refine ⟨7799447991303953473945373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5199631994202635649296915 7799447991303953473945373)
                    ·
                      refine ⟨2924792996738982552729515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7799447991303953473945373 2924792996738982552729515)
                      ·
                        rfl

theorem cell23_5696014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 3, 1, 1, 3].length) (baseStart_5696014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5696014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5696014 prefixEnd_5696014 := by exact prefixLift 5696014
  have htrace : WordTrace (prefixWord ++ tailWord_5696014) baseStart_5696014 baseEnd_5696014 := by
    simpa [prefixWord, tailWord_5696014, baseEnd_5696014] using wordTrace_append hprefix tailTrace_5696014
  have hstable : (prefixWord ++ tailWord_5696014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5696014).length < 2 ^ (prefixWord ++ tailWord_5696014).sum := by decide
  have hdescent : baseEnd_5696014 < baseStart_5696014 := by decide
  rcases family_descends (prefixWord ++ tailWord_5696014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5696037 : List Nat := [1, 3, 1, 2, 2, 1, 2, 6, 1, 2, 2]
def baseStart_5696037 : Nat := 118140960795 + 5696037 * 2 ^ 59
def prefixEnd_5696037 : Nat := 4983230072969 + 3 ^ 40 * 5696037 * 2
def baseEnd_5696037 : Nat := 2924804806794035962741909

theorem tailTrace_5696037 : CollatzResearch.WordTrace tailWord_5696037 prefixEnd_5696037 2924804806794035962741909 := by
  unfold tailWord_5696037
  simp only [CollatzResearch.WordTrace]
  refine ⟨207751536865238229515694365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138501024576825486343796243 207751536865238229515694365)
  ·
    refine ⟨77906826324464336068385387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207751536865238229515694365 77906826324464336068385387)
    ·
      refine ⟨116860239486696504102578081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77906826324464336068385387 116860239486696504102578081)
      ·
        refine ⟨87645179615022378076933561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116860239486696504102578081 87645179615022378076933561)
        ·
          refine ⟨65733884711266783557700171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87645179615022378076933561 65733884711266783557700171)
          ·
            refine ⟨98600827066900175336550257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65733884711266783557700171 98600827066900175336550257)
            ·
              refine ⟨73950620300175131502412693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98600827066900175336550257 73950620300175131502412693)
              ·
                refine ⟨3466435326570709289175595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 73950620300175131502412693 3466435326570709289175595)
                ·
                  refine ⟨5199652989856063933763393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3466435326570709289175595 5199652989856063933763393)
                  ·
                    refine ⟨3899739742392047950322545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5199652989856063933763393 3899739742392047950322545)
                    ·
                      refine ⟨2924804806794035962741909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3899739742392047950322545 2924804806794035962741909)
                      ·
                        rfl

theorem cell23_5696037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 6, 1, 2, 2].length) (baseStart_5696037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5696037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5696037 prefixEnd_5696037 := by exact prefixLift 5696037
  have htrace : WordTrace (prefixWord ++ tailWord_5696037) baseStart_5696037 baseEnd_5696037 := by
    simpa [prefixWord, tailWord_5696037, baseEnd_5696037] using wordTrace_append hprefix tailTrace_5696037
  have hstable : (prefixWord ++ tailWord_5696037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5696037).length < 2 ^ (prefixWord ++ tailWord_5696037).sum := by decide
  have hdescent : baseEnd_5696037 < baseStart_5696037 := by decide
  rcases family_descends (prefixWord ++ tailWord_5696037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5696053 : List Nat := [1, 3, 3, 1, 1, 2, 2, 3, 1, 3, 3]
def baseStart_5696053 : Nat := 118140960795 + 5696053 * 2 ^ 59
def prefixEnd_5696053 : Nat := 4983230072969 + 3 ^ 40 * 5696053 * 2
def baseEnd_5696053 : Nat := 2924813022484507900141835

theorem tailTrace_5696053 : CollatzResearch.WordTrace tailWord_5696053 prefixEnd_5696053 2924813022484507900141835 := by
  unfold tailWord_5696053
  simp only [CollatzResearch.WordTrace]
  refine ⟨207752120433180264248276813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138501413622120176165517875 207752120433180264248276813)
  ·
    refine ⟨77907045162442599093103805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207752120433180264248276813 77907045162442599093103805)
    ·
      refine ⟨29215141935915974659913927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77907045162442599093103805 29215141935915974659913927)
      ·
        refine ⟨43822712903873961989870891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29215141935915974659913927 43822712903873961989870891)
        ·
          refine ⟨65734069355810942984806337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43822712903873961989870891 65734069355810942984806337)
          ·
            refine ⟨49300552016858207238604753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65734069355810942984806337 49300552016858207238604753)
            ·
              refine ⟨36975414012643655428953565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49300552016858207238604753 36975414012643655428953565)
              ·
                refine ⟨13865780254741370785857587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36975414012643655428953565 13865780254741370785857587)
                ·
                  refine ⟨20798670382112056178786381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13865780254741370785857587 20798670382112056178786381)
                  ·
                    refine ⟨7799501393292021067044893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20798670382112056178786381 7799501393292021067044893)
                    ·
                      refine ⟨2924813022484507900141835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7799501393292021067044893 2924813022484507900141835)
                      ·
                        rfl

theorem cell23_5696053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_5696053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5696053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5696053 prefixEnd_5696053 := by exact prefixLift 5696053
  have htrace : WordTrace (prefixWord ++ tailWord_5696053) baseStart_5696053 baseEnd_5696053 := by
    simpa [prefixWord, tailWord_5696053, baseEnd_5696053] using wordTrace_append hprefix tailTrace_5696053
  have hstable : (prefixWord ++ tailWord_5696053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5696053).length < 2 ^ (prefixWord ++ tailWord_5696053).sum := by decide
  have hdescent : baseEnd_5696053 < baseStart_5696053 := by decide
  rcases family_descends (prefixWord ++ tailWord_5696053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5696094 : List Nat := [4, 4, 1, 2, 1, 2, 1, 8]
def baseStart_5696094 : Nat := 118140960795 + 5696094 * 2 ^ 59
def prefixEnd_5696094 : Nat := 4983230072969 + 3 ^ 40 * 5696094 * 2
def baseEnd_5696094 : Nat := 108327187970049712582561

theorem tailTrace_5696094 : CollatzResearch.WordTrace tailWord_5696094 prefixEnd_5696094 108327187970049712582561 := by
  unfold tailWord_5696094
  simp only [CollatzResearch.WordTrace]
  refine ⟨25969201978253966031314917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138502410550687818833679557 25969201978253966031314917)
  ·
    refine ⟨4869225370922618630871547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25969201978253966031314917 4869225370922618630871547)
    ·
      refine ⟨7303838056383927946307321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4869225370922618630871547 7303838056383927946307321)
      ·
        refine ⟨5477878542287945959730491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7303838056383927946307321 5477878542287945959730491)
        ·
          refine ⟨8216817813431918939595737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5477878542287945959730491 8216817813431918939595737)
          ·
            refine ⟨6162613360073939204696803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8216817813431918939595737 6162613360073939204696803)
            ·
              refine ⟨9243920040110908807045205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6162613360073939204696803 9243920040110908807045205)
              ·
                refine ⟨108327187970049712582561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9243920040110908807045205 108327187970049712582561)
                ·
                  rfl

theorem cell23_5696094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 8].length) (baseStart_5696094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5696094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5696094 prefixEnd_5696094 := by exact prefixLift 5696094
  have htrace : WordTrace (prefixWord ++ tailWord_5696094) baseStart_5696094 baseEnd_5696094 := by
    simpa [prefixWord, tailWord_5696094, baseEnd_5696094] using wordTrace_append hprefix tailTrace_5696094
  have hstable : (prefixWord ++ tailWord_5696094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5696094).length < 2 ^ (prefixWord ++ tailWord_5696094).sum := by decide
  have hdescent : baseEnd_5696094 < baseStart_5696094 := by decide
  rcases family_descends (prefixWord ++ tailWord_5696094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5696096 : List Nat := [2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 5]
def baseStart_5696096 : Nat := 118140960795 + 5696096 * 2 ^ 59
def prefixEnd_5696096 : Nat := 4983230072969 + 3 ^ 40 * 5696096 * 2
def baseEnd_5696096 : Nat := 2924835102152651231904137

theorem tailTrace_5696096 : CollatzResearch.WordTrace tailWord_5696096 prefixEnd_5696096 2924835102152651231904137 := by
  unfold tailWord_5696096
  simp only [CollatzResearch.WordTrace]
  refine ⟨103876844386012241296046071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138502459181349655061394761 103876844386012241296046071)
  ·
    refine ⟨155815266579018361944069107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103876844386012241296046071 155815266579018361944069107)
    ·
      refine ⟨233722899868527542916103661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155815266579018361944069107 233722899868527542916103661)
      ·
        refine ⟨87646087450697828593538873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 233722899868527542916103661 87646087450697828593538873)
        ·
          refine ⟨65734565588023371445154155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87646087450697828593538873 65734565588023371445154155)
          ·
            refine ⟨98601848382035057167731233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65734565588023371445154155 98601848382035057167731233)
            ·
              refine ⟨73951386286526292875798425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98601848382035057167731233 73951386286526292875798425)
              ·
                refine ⟨55463539714894719656848819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73951386286526292875798425 55463539714894719656848819)
                ·
                  refine ⟨83195309572342079485273229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55463539714894719656848819 83195309572342079485273229)
                  ·
                    refine ⟨31198241089628279806977461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 83195309572342079485273229 31198241089628279806977461)
                    ·
                      refine ⟨2924835102152651231904137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31198241089628279806977461 2924835102152651231904137)
                      ·
                        rfl

theorem cell23_5696096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_5696096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5696096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5696096 prefixEnd_5696096 := by exact prefixLift 5696096
  have htrace : WordTrace (prefixWord ++ tailWord_5696096) baseStart_5696096 baseEnd_5696096 := by
    simpa [prefixWord, tailWord_5696096, baseEnd_5696096] using wordTrace_append hprefix tailTrace_5696096
  have hstable : (prefixWord ++ tailWord_5696096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5696096).length < 2 ^ (prefixWord ++ tailWord_5696096).sum := by decide
  have hdescent : baseEnd_5696096 < baseStart_5696096 := by decide
  rcases family_descends (prefixWord ++ tailWord_5696096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5696161 : List Nat := [1, 2, 3, 3, 3, 1, 3, 1, 2, 2, 2]
def baseStart_5696161 : Nat := 118140960795 + 5696161 * 2 ^ 59
def prefixEnd_5696161 : Nat := 4983230072969 + 3 ^ 40 * 5696161 * 2
def baseEnd_5696161 : Nat := 2924868478395193477591339

theorem tailTrace_5696161 : CollatzResearch.WordTrace tailWord_5696161 prefixEnd_5696161 2924868478395193477591339 := by
  unfold tailWord_5696161
  simp only [CollatzResearch.WordTrace]
  refine ⟨207756059516788998693208337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138504039677859332462138891 207756059516788998693208337)
  ·
    refine ⟨155817044637591749019906253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207756059516788998693208337 155817044637591749019906253)
    ·
      refine ⟨58431391739096905882464845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155817044637591749019906253 58431391739096905882464845)
      ·
        refine ⟨21911771902161339705924317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58431391739096905882464845 21911771902161339705924317)
        ·
          refine ⟨8216914463310502389721619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21911771902161339705924317 8216914463310502389721619)
          ·
            refine ⟨12325371694965753584582429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8216914463310502389721619 12325371694965753584582429)
            ·
              refine ⟨4622014385612157594218411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12325371694965753584582429 4622014385612157594218411)
              ·
                refine ⟨6933021578418236391327617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4622014385612157594218411 6933021578418236391327617)
                ·
                  refine ⟨5199766183813677293495713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6933021578418236391327617 5199766183813677293495713)
                  ·
                    refine ⟨3899824637860257970121785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5199766183813677293495713 3899824637860257970121785)
                    ·
                      refine ⟨2924868478395193477591339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3899824637860257970121785 2924868478395193477591339)
                      ·
                        rfl

theorem cell23_5696161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_5696161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5696161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5696161 prefixEnd_5696161 := by exact prefixLift 5696161
  have htrace : WordTrace (prefixWord ++ tailWord_5696161) baseStart_5696161 baseEnd_5696161 := by
    simpa [prefixWord, tailWord_5696161, baseEnd_5696161] using wordTrace_append hprefix tailTrace_5696161
  have hstable : (prefixWord ++ tailWord_5696161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5696161).length < 2 ^ (prefixWord ++ tailWord_5696161).sum := by decide
  have hdescent : baseEnd_5696161 < baseStart_5696161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5696161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5696176 : List Nat := [2, 1, 1, 1, 2, 1, 3, 1, 1, 10]
def baseStart_5696176 : Nat := 118140960795 + 5696176 * 2 ^ 59
def prefixEnd_5696176 : Nat := 4983230072969 + 3 ^ 40 * 5696176 * 2
def baseEnd_5696176 : Nat := 974958726868336972967923

theorem tailTrace_5696176 : CollatzResearch.WordTrace tailWord_5696176 prefixEnd_5696176 974958726868336972967923 := by
  unfold tailWord_5696176
  simp only [CollatzResearch.WordTrace]
  refine ⟨103878303305867328127502191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138504404407823104170002921 103878303305867328127502191)
  ·
    refine ⟨155817454958800992191253287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103878303305867328127502191 155817454958800992191253287)
    ·
      refine ⟨233726182438201488286879931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155817454958800992191253287 233726182438201488286879931)
      ·
        refine ⟨350589273657302232430319897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233726182438201488286879931 350589273657302232430319897)
        ·
          refine ⟨262941955242976674322739923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 350589273657302232430319897 262941955242976674322739923)
          ·
            refine ⟨394412932864465011484109885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262941955242976674322739923 394412932864465011484109885)
            ·
              refine ⟨147904849824174379306541207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 394412932864465011484109885 147904849824174379306541207)
              ·
                refine ⟨221857274736261568959811811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147904849824174379306541207 221857274736261568959811811)
                ·
                  refine ⟨332785912104392353439717717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 221857274736261568959811811 332785912104392353439717717)
                  ·
                    refine ⟨974958726868336972967923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 332785912104392353439717717 974958726868336972967923)
                    ·
                      rfl

theorem cell23_5696176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 1, 10].length) (baseStart_5696176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5696176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5696176 prefixEnd_5696176 := by exact prefixLift 5696176
  have htrace : WordTrace (prefixWord ++ tailWord_5696176) baseStart_5696176 baseEnd_5696176 := by
    simpa [prefixWord, tailWord_5696176, baseEnd_5696176] using wordTrace_append hprefix tailTrace_5696176
  have hstable : (prefixWord ++ tailWord_5696176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5696176).length < 2 ^ (prefixWord ++ tailWord_5696176).sum := by decide
  have hdescent : baseEnd_5696176 < baseStart_5696176 := by decide
  rcases family_descends (prefixWord ++ tailWord_5696176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5696200 : List Nat := [2, 1, 3, 1, 2, 4, 1, 2, 2, 1, 4]
def baseStart_5696200 : Nat := 118140960795 + 5696200 * 2 ^ 59
def prefixEnd_5696200 : Nat := 4983230072969 + 3 ^ 40 * 5696200 * 2
def baseEnd_5696200 : Nat := 2924888504140718825003659

theorem tailTrace_5696200 : CollatzResearch.WordTrace tailWord_5696200 prefixEnd_5696200 2924888504140718825003659 := by
  unfold tailWord_5696200
  simp only [CollatzResearch.WordTrace]
  refine ⟨103878740981823854176939027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138504987975765138902585369 103878740981823854176939027)
  ·
    refine ⟨155818111472735781265408541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103878740981823854176939027 155818111472735781265408541)
    ·
      refine ⟨58431791802275917974528203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155818111472735781265408541 58431791802275917974528203)
      ·
        refine ⟨87647687703413876961792305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58431791802275917974528203 87647687703413876961792305)
        ·
          refine ⟨65735765777560407721344229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87647687703413876961792305 65735765777560407721344229)
          ·
            refine ⟨12325456083292576447752043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65735765777560407721344229 12325456083292576447752043)
            ·
              refine ⟨18488184124938864671628065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12325456083292576447752043 18488184124938864671628065)
              ·
                refine ⟨13866138093704148503721049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18488184124938864671628065 13866138093704148503721049)
                ·
                  refine ⟨10399603570278111377790787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13866138093704148503721049 10399603570278111377790787)
                  ·
                    refine ⟨15599405355417167066686181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10399603570278111377790787 15599405355417167066686181)
                    ·
                      refine ⟨2924888504140718825003659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15599405355417167066686181 2924888504140718825003659)
                      ·
                        rfl

theorem cell23_5696200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 2, 2, 1, 4].length) (baseStart_5696200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5696200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5696200 prefixEnd_5696200 := by exact prefixLift 5696200
  have htrace : WordTrace (prefixWord ++ tailWord_5696200) baseStart_5696200 baseEnd_5696200 := by
    simpa [prefixWord, tailWord_5696200, baseEnd_5696200] using wordTrace_append hprefix tailTrace_5696200
  have hstable : (prefixWord ++ tailWord_5696200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5696200).length < 2 ^ (prefixWord ++ tailWord_5696200).sum := by decide
  have hdescent : baseEnd_5696200 < baseStart_5696200 := by decide
  rcases family_descends (prefixWord ++ tailWord_5696200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5696233 : List Nat := [1, 2, 1, 1, 1, 2, 4, 1, 2, 5, 3]
def baseStart_5696233 : Nat := 118140960795 + 5696233 * 2 ^ 59
def prefixEnd_5696233 : Nat := 4983230072969 + 3 ^ 40 * 5696233 * 2
def baseEnd_5696233 : Nat := 2924905449002317195891007

theorem tailTrace_5696233 : CollatzResearch.WordTrace tailWord_5696233 prefixEnd_5696233 2924905449002317195891007 := by
  unfold tailWord_5696233
  simp only [CollatzResearch.WordTrace]
  refine ⟨207758685572528154989829353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138505790381685436659886235 207758685572528154989829353)
  ·
    refine ⟨155819014179396116242372015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207758685572528154989829353 155819014179396116242372015)
    ·
      refine ⟨233728521269094174363558023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155819014179396116242372015 233728521269094174363558023)
      ·
        refine ⟨350592781903641261545337035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233728521269094174363558023 350592781903641261545337035)
        ·
          refine ⟨525889172855461892318005553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350592781903641261545337035 525889172855461892318005553)
          ·
            refine ⟨394416879641596419238504165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 525889172855461892318005553 394416879641596419238504165)
            ·
              refine ⟨73953164932799328607219531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 394416879641596419238504165 73953164932799328607219531)
              ·
                refine ⟨110929747399198992910829297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73953164932799328607219531 110929747399198992910829297)
                ·
                  refine ⟨83197310549399244683121973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110929747399198992910829297 83197310549399244683121973)
                  ·
                    refine ⟨7799747864006179189042685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 83197310549399244683121973 7799747864006179189042685)
                    ·
                      refine ⟨2924905449002317195891007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7799747864006179189042685 2924905449002317195891007)
                      ·
                        rfl

theorem cell23_5696233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 5, 3].length) (baseStart_5696233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5696233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5696233 prefixEnd_5696233 := by exact prefixLift 5696233
  have htrace : WordTrace (prefixWord ++ tailWord_5696233) baseStart_5696233 baseEnd_5696233 := by
    simpa [prefixWord, tailWord_5696233, baseEnd_5696233] using wordTrace_append hprefix tailTrace_5696233
  have hstable : (prefixWord ++ tailWord_5696233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5696233).length < 2 ^ (prefixWord ++ tailWord_5696233).sum := by decide
  have hdescent : baseEnd_5696233 < baseStart_5696233 := by decide
  rcases family_descends (prefixWord ++ tailWord_5696233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5696237 : List Nat := [1, 5, 1, 2, 1, 1, 4, 1, 2, 2, 3]
def baseStart_5696237 : Nat := 118140960795 + 5696237 * 2 ^ 59
def prefixEnd_5696237 : Nat := 4983230072969 + 3 ^ 40 * 5696237 * 2
def baseEnd_5696237 : Nat := 2924907502924935180240989

theorem tailTrace_5696237 : CollatzResearch.WordTrace tailWord_5696237 prefixEnd_5696237 2924907502924935180240989 := by
  unfold tailWord_5696237
  simp only [CollatzResearch.WordTrace]
  refine ⟨207758831464513663672974965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138505887643009109115316643 207758831464513663672974965)
  ·
    refine ⟨19477390449798155969341403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 207758831464513663672974965 19477390449798155969341403)
    ·
      refine ⟨29216085674697233954012105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19477390449798155969341403 29216085674697233954012105)
      ·
        refine ⟨21912064256022925465509079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29216085674697233954012105 21912064256022925465509079)
        ·
          refine ⟨32868096384034388198263619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21912064256022925465509079 32868096384034388198263619)
          ·
            refine ⟨49302144576051582297395429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32868096384034388198263619 49302144576051582297395429)
            ·
              refine ⟨9244152108009671680761643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49302144576051582297395429 9244152108009671680761643)
              ·
                refine ⟨13866228162014507521142465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9244152108009671680761643 13866228162014507521142465)
                ·
                  refine ⟨10399671121510880640856849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13866228162014507521142465 10399671121510880640856849)
                  ·
                    refine ⟨7799753341133160480642637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10399671121510880640856849 7799753341133160480642637)
                    ·
                      refine ⟨2924907502924935180240989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7799753341133160480642637 2924907502924935180240989)
                      ·
                        rfl

theorem cell23_5696237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_5696237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5696237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5696237 prefixEnd_5696237 := by exact prefixLift 5696237
  have htrace : WordTrace (prefixWord ++ tailWord_5696237) baseStart_5696237 baseEnd_5696237 := by
    simpa [prefixWord, tailWord_5696237, baseEnd_5696237] using wordTrace_append hprefix tailTrace_5696237
  have hstable : (prefixWord ++ tailWord_5696237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5696237).length < 2 ^ (prefixWord ++ tailWord_5696237).sum := by decide
  have hdescent : baseEnd_5696237 < baseStart_5696237 := by decide
  rcases family_descends (prefixWord ++ tailWord_5696237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5696300 : List Nat := [2, 2, 1, 1, 1, 4, 2, 2, 4, 4]
def baseStart_5696300 : Nat := 118140960795 + 5696300 * 2 ^ 59
def prefixEnd_5696300 : Nat := 4983230072969 + 3 ^ 40 * 5696300 * 2
def baseEnd_5696300 : Nat := 974979950735389477917733

theorem tailTrace_5696300 : CollatzResearch.WordTrace tailWord_5696300 prefixEnd_5696300 974979950735389477917733 := by
  unfold tailWord_5696300
  simp only [CollatzResearch.WordTrace]
  refine ⟨103880564631642712716259177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138507419508856950288345569 103880564631642712716259177)
  ·
    refine ⟨77910423473732034537194383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103880564631642712716259177 77910423473732034537194383)
    ·
      refine ⟨116865635210598051805791575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77910423473732034537194383 116865635210598051805791575)
      ·
        refine ⟨175298452815897077708687363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116865635210598051805791575 175298452815897077708687363)
        ·
          refine ⟨262947679223845616563031045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175298452815897077708687363 262947679223845616563031045)
          ·
            refine ⟨49302689854471053105568321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 262947679223845616563031045 49302689854471053105568321)
            ·
              refine ⟨36977017390853289829176241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49302689854471053105568321 36977017390853289829176241)
              ·
                refine ⟨27732763043139967371882181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36977017390853289829176241 27732763043139967371882181)
                ·
                  refine ⟨5199893070588743882227909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27732763043139967371882181 5199893070588743882227909)
                  ·
                    refine ⟨974979950735389477917733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5199893070588743882227909 974979950735389477917733)
                    ·
                      rfl

theorem cell23_5696300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 4].length) (baseStart_5696300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5696300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5696300 prefixEnd_5696300 := by exact prefixLift 5696300
  have htrace : WordTrace (prefixWord ++ tailWord_5696300) baseStart_5696300 baseEnd_5696300 := by
    simpa [prefixWord, tailWord_5696300, baseEnd_5696300] using wordTrace_append hprefix tailTrace_5696300
  have hstable : (prefixWord ++ tailWord_5696300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5696300).length < 2 ^ (prefixWord ++ tailWord_5696300).sum := by decide
  have hdescent : baseEnd_5696300 < baseStart_5696300 := by decide
  rcases family_descends (prefixWord ++ tailWord_5696300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5696307 : List Nat := [1, 1, 1, 2, 6, 2, 1, 3, 1, 1, 4]
def baseStart_5696307 : Nat := 118140960795 + 5696307 * 2 ^ 59
def prefixEnd_5696307 : Nat := 4983230072969 + 3 ^ 40 * 5696307 * 2
def baseEnd_5696307 : Nat := 2924943446570749906365667

theorem tailTrace_5696307 : CollatzResearch.WordTrace tailWord_5696307 prefixEnd_5696307 2924943446570749906365667 := by
  unfold tailWord_5696307
  simp only [CollatzResearch.WordTrace]
  refine ⟨207761384574260065628023175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138507589716173377085348783 207761384574260065628023175)
  ·
    refine ⟨311642076861390098442034763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207761384574260065628023175 311642076861390098442034763)
    ·
      refine ⟨467463115292085147663052145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311642076861390098442034763 467463115292085147663052145)
      ·
        refine ⟨350597336469063860747289109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 467463115292085147663052145 350597336469063860747289109)
        ·
          refine ⟨16434250146987368472529177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 350597336469063860747289109 16434250146987368472529177)
          ·
            refine ⟨12325687610240526354396883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16434250146987368472529177 12325687610240526354396883)
            ·
              refine ⟨18488531415360789531595325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12325687610240526354396883 18488531415360789531595325)
              ·
                refine ⟨6933199280760296074348247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18488531415360789531595325 6933199280760296074348247)
                ·
                  refine ⟨10399798921140444111522371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6933199280760296074348247 10399798921140444111522371)
                  ·
                    refine ⟨15599698381710666167283557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10399798921140444111522371 15599698381710666167283557)
                    ·
                      refine ⟨2924943446570749906365667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15599698381710666167283557 2924943446570749906365667)
                      ·
                        rfl

theorem cell23_5696307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 3, 1, 1, 4].length) (baseStart_5696307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5696307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5696307 prefixEnd_5696307 := by exact prefixLift 5696307
  have htrace : WordTrace (prefixWord ++ tailWord_5696307) baseStart_5696307 baseEnd_5696307 := by
    simpa [prefixWord, tailWord_5696307, baseEnd_5696307] using wordTrace_append hprefix tailTrace_5696307
  have hstable : (prefixWord ++ tailWord_5696307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5696307).length < 2 ^ (prefixWord ++ tailWord_5696307).sum := by decide
  have hdescent : baseEnd_5696307 < baseStart_5696307 := by decide
  rcases family_descends (prefixWord ++ tailWord_5696307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5696357 : List Nat := [1, 3, 1, 3, 1, 1, 3, 2, 4, 1, 3]
def baseStart_5696357 : Nat := 118140960795 + 5696357 * 2 ^ 59
def prefixEnd_5696357 : Nat := 4983230072969 + 3 ^ 40 * 5696357 * 2
def baseEnd_5696357 : Nat := 2924969120603474710740437

theorem tailTrace_5696357 : CollatzResearch.WordTrace tailWord_5696357 prefixEnd_5696357 2924969120603474710740437 := by
  unfold tailWord_5696357
  simp only [CollatzResearch.WordTrace]
  refine ⟨207763208224078924167343325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138508805482719282778228883 207763208224078924167343325)
  ·
    refine ⟨77911203084029596562753747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207763208224078924167343325 77911203084029596562753747)
    ·
      refine ⟨116866804626044394844130621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77911203084029596562753747 116866804626044394844130621)
      ·
        refine ⟨43825051734766648066548983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116866804626044394844130621 43825051734766648066548983)
        ·
          refine ⟨65737577602149972099823475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43825051734766648066548983 65737577602149972099823475)
          ·
            refine ⟨98606366403224958149735213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65737577602149972099823475 98606366403224958149735213)
            ·
              refine ⟨36977387401209359306150705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98606366403224958149735213 36977387401209359306150705)
              ·
                refine ⟨27733040550907019479613029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36977387401209359306150705 27733040550907019479613029)
                ·
                  refine ⟨5199945103295066152427443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27733040550907019479613029 5199945103295066152427443)
                  ·
                    refine ⟨7799917654942599228641165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5199945103295066152427443 7799917654942599228641165)
                    ·
                      refine ⟨2924969120603474710740437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7799917654942599228641165 2924969120603474710740437)
                      ·
                        rfl

theorem cell23_5696357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 4, 1, 3].length) (baseStart_5696357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5696357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5696357 prefixEnd_5696357 := by exact prefixLift 5696357
  have htrace : WordTrace (prefixWord ++ tailWord_5696357) baseStart_5696357 baseEnd_5696357 := by
    simpa [prefixWord, tailWord_5696357, baseEnd_5696357] using wordTrace_append hprefix tailTrace_5696357
  have hstable : (prefixWord ++ tailWord_5696357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5696357).length < 2 ^ (prefixWord ++ tailWord_5696357).sum := by decide
  have hdescent : baseEnd_5696357 < baseStart_5696357 := by decide
  rcases family_descends (prefixWord ++ tailWord_5696357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5696391 : List Nat := [1, 1, 4, 2, 3, 1, 4, 1, 2, 1, 3]
def baseStart_5696391 : Nat := 118140960795 + 5696391 * 2 ^ 59
def prefixEnd_5696391 : Nat := 4983230072969 + 3 ^ 40 * 5696391 * 2
def baseEnd_5696391 : Nat := 2924986578945727577715281

theorem tailTrace_5696391 : CollatzResearch.WordTrace tailWord_5696391 prefixEnd_5696391 2924986578945727577715281 := by
  unfold tailWord_5696391
  simp only [CollatzResearch.WordTrace]
  refine ⟨207764448305955747974081027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138509632203970498649387351 207764448305955747974081027)
  ·
    refine ⟨311646672458933621961121541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207764448305955747974081027 311646672458933621961121541)
    ·
      refine ⟨58433751086050054117710289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 311646672458933621961121541 58433751086050054117710289)
      ·
        refine ⟨43825313314537540588282717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58433751086050054117710289 43825313314537540588282717)
        ·
          refine ⟨16434492492951577720606019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43825313314537540588282717 16434492492951577720606019)
          ·
            refine ⟨24651738739427366580909029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16434492492951577720606019 24651738739427366580909029)
            ·
              refine ⟨4622201013642631233920443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24651738739427366580909029 4622201013642631233920443)
              ·
                refine ⟨6933301520463946850880665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4622201013642631233920443 6933301520463946850880665)
                ·
                  refine ⟨5199976140347960138160499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6933301520463946850880665 5199976140347960138160499)
                  ·
                    refine ⟨7799964210521940207240749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5199976140347960138160499 7799964210521940207240749)
                    ·
                      refine ⟨2924986578945727577715281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7799964210521940207240749 2924986578945727577715281)
                      ·
                        rfl

theorem cell23_5696391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 1, 2, 1, 3].length) (baseStart_5696391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5696391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5696391 prefixEnd_5696391 := by exact prefixLift 5696391
  have htrace : WordTrace (prefixWord ++ tailWord_5696391) baseStart_5696391 baseEnd_5696391 := by
    simpa [prefixWord, tailWord_5696391, baseEnd_5696391] using wordTrace_append hprefix tailTrace_5696391
  have hstable : (prefixWord ++ tailWord_5696391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5696391).length < 2 ^ (prefixWord ++ tailWord_5696391).sum := by decide
  have hdescent : baseEnd_5696391 < baseStart_5696391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5696391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5696417 : List Nat := [1, 2, 3, 4, 1, 1, 2, 1, 2, 1, 5]
def baseStart_5696417 : Nat := 118140960795 + 5696417 * 2 ^ 59
def prefixEnd_5696417 : Nat := 4983230072969 + 3 ^ 40 * 5696417 * 2
def baseEnd_5696417 : Nat := 2924999929442744475990161

theorem tailTrace_5696417 : CollatzResearch.WordTrace tailWord_5696417 prefixEnd_5696417 2924999929442744475990161 := by
  unfold tailWord_5696417
  simp only [CollatzResearch.WordTrace]
  refine ⟨207765396603861554414527505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138510264402574369609685003 207765396603861554414527505)
  ·
    refine ⟨155824047452896165810895629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207765396603861554414527505 155824047452896165810895629)
    ·
      refine ⟨58434017794836062179085861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155824047452896165810895629 58434017794836062179085861)
      ·
        refine ⟨10956378336531761658578599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58434017794836062179085861 10956378336531761658578599)
        ·
          refine ⟨16434567504797642487867899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10956378336531761658578599 16434567504797642487867899)
          ·
            refine ⟨24651851257196463731801849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16434567504797642487867899 24651851257196463731801849)
            ·
              refine ⟨18488888442897347798851387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24651851257196463731801849 18488888442897347798851387)
              ·
                refine ⟨27733332664346021698277081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18488888442897347798851387 27733332664346021698277081)
                ·
                  refine ⟨20799999498259516273707811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27733332664346021698277081 20799999498259516273707811)
                  ·
                    refine ⟨31199999247389274410561717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20799999498259516273707811 31199999247389274410561717)
                    ·
                      refine ⟨2924999929442744475990161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31199999247389274410561717 2924999929442744475990161)
                      ·
                        rfl

theorem cell23_5696417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_5696417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5696417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5696417 prefixEnd_5696417 := by exact prefixLift 5696417
  have htrace : WordTrace (prefixWord ++ tailWord_5696417) baseStart_5696417 baseEnd_5696417 := by
    simpa [prefixWord, tailWord_5696417, baseEnd_5696417] using wordTrace_append hprefix tailTrace_5696417
  have hstable : (prefixWord ++ tailWord_5696417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5696417).length < 2 ^ (prefixWord ++ tailWord_5696417).sum := by decide
  have hdescent : baseEnd_5696417 < baseStart_5696417 := by decide
  rcases family_descends (prefixWord ++ tailWord_5696417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5696418 : List Nat := [3, 3, 1, 2, 2, 2, 3, 1, 1, 3, 2]
def baseStart_5696418 : Nat := 118140960795 + 5696418 * 2 ^ 59
def prefixEnd_5696418 : Nat := 4983230072969 + 3 ^ 40 * 5696418 * 2
def baseEnd_5696418 : Nat := 2925000442923398972077657

theorem tailTrace_5696418 : CollatzResearch.WordTrace tailWord_5696418 prefixEnd_5696418 2925000442923398972077657 := by
  unfold tailWord_5696418
  simp only [CollatzResearch.WordTrace]
  refine ⟨51941358269214482896328477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138510288717905287723542605 51941358269214482896328477)
  ·
    refine ⟨19478009350955431086123179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51941358269214482896328477 19478009350955431086123179)
    ·
      refine ⟨29217014026433146629184769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19478009350955431086123179 29217014026433146629184769)
      ·
        refine ⟨21912760519824859971888577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29217014026433146629184769 21912760519824859971888577)
        ·
          refine ⟨16434570389868644978916433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21912760519824859971888577 16434570389868644978916433)
          ·
            refine ⟨12325927792401483734187325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16434570389868644978916433 12325927792401483734187325)
            ·
              refine ⟨4622222922150556400320247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12325927792401483734187325 4622222922150556400320247)
              ·
                refine ⟨6933334383225834600480371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4622222922150556400320247 6933334383225834600480371)
                ·
                  refine ⟨10400001574838751900720557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6933334383225834600480371 10400001574838751900720557)
                  ·
                    refine ⟨3900000590564531962770209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10400001574838751900720557 3900000590564531962770209)
                    ·
                      refine ⟨2925000442923398972077657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3900000590564531962770209 2925000442923398972077657)
                      ·
                        rfl

theorem cell23_5696418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_5696418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5696418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5696418 prefixEnd_5696418 := by exact prefixLift 5696418
  have htrace : WordTrace (prefixWord ++ tailWord_5696418) baseStart_5696418 baseEnd_5696418 := by
    simpa [prefixWord, tailWord_5696418, baseEnd_5696418] using wordTrace_append hprefix tailTrace_5696418
  have hstable : (prefixWord ++ tailWord_5696418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5696418).length < 2 ^ (prefixWord ++ tailWord_5696418).sum := by decide
  have hdescent : baseEnd_5696418 < baseStart_5696418 := by decide
  rcases family_descends (prefixWord ++ tailWord_5696418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5696541 : List Nat := [1, 4, 2, 2, 3, 1, 1, 2, 2, 2, 3]
def baseStart_5696541 : Nat := 118140960795 + 5696541 * 2 ^ 59
def prefixEnd_5696541 : Nat := 4983230072969 + 3 ^ 40 * 5696541 * 2
def baseEnd_5696541 : Nat := 2925063601043901990839591

theorem tailTrace_5696541 : CollatzResearch.WordTrace tailWord_5696541 prefixEnd_5696541 2925063601043901990839591 := by
  unfold tailWord_5696541
  simp only [CollatzResearch.WordTrace]
  refine ⟨207769919255412323592041477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138513279503608215728027651 207769919255412323592041477)
  ·
    refine ⟨38956859860389810673507777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 207769919255412323592041477 38956859860389810673507777)
    ·
      refine ⟨29217644895292358005130833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38956859860389810673507777 29217644895292358005130833)
      ·
        refine ⟨21913233671469268503848125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29217644895292358005130833 21913233671469268503848125)
        ·
          refine ⟨8217462626800975688943047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21913233671469268503848125 8217462626800975688943047)
          ·
            refine ⟨12326193940201463533414571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8217462626800975688943047 12326193940201463533414571)
            ·
              refine ⟨18489290910302195300121857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12326193940201463533414571 18489290910302195300121857)
              ·
                refine ⟨13866968182726646475091393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18489290910302195300121857 13866968182726646475091393)
                ·
                  refine ⟨10400226137044984856318545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13866968182726646475091393 10400226137044984856318545)
                  ·
                    refine ⟨7800169602783738642238909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10400226137044984856318545 7800169602783738642238909)
                    ·
                      refine ⟨2925063601043901990839591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7800169602783738642238909 2925063601043901990839591)
                      ·
                        rfl

theorem cell23_5696541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_5696541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5696541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5696541 prefixEnd_5696541 := by exact prefixLift 5696541
  have htrace : WordTrace (prefixWord ++ tailWord_5696541) baseStart_5696541 baseEnd_5696541 := by
    simpa [prefixWord, tailWord_5696541, baseEnd_5696541] using wordTrace_append hprefix tailTrace_5696541
  have hstable : (prefixWord ++ tailWord_5696541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5696541).length < 2 ^ (prefixWord ++ tailWord_5696541).sum := by decide
  have hdescent : baseEnd_5696541 < baseStart_5696541 := by decide
  rcases family_descends (prefixWord ++ tailWord_5696541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5696607 : List Nat := [1, 1, 2, 3, 1, 1, 3, 2, 3, 2, 4]
def baseStart_5696607 : Nat := 118140960795 + 5696607 * 2 ^ 59
def prefixEnd_5696607 : Nat := 4983230072969 + 3 ^ 40 * 5696607 * 2
def baseEnd_5696607 : Nat := 2925097490767098732614287

theorem tailTrace_5696607 : CollatzResearch.WordTrace tailWord_5696607 prefixEnd_5696607 2925097490767098732614287 := by
  unfold tailWord_5696607
  simp only [CollatzResearch.WordTrace]
  refine ⟨207772326473173216863944075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138514884315448811242629383 207772326473173216863944075)
  ·
    refine ⟨311658489709759825295916113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207772326473173216863944075 311658489709759825295916113)
    ·
      refine ⟨233743867282319868971937085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311658489709759825295916113 233743867282319868971937085)
      ·
        refine ⟨87653950230869950864476407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 233743867282319868971937085 87653950230869950864476407)
        ·
          refine ⟨131480925346304926296714611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87653950230869950864476407 131480925346304926296714611)
          ·
            refine ⟨197221388019457389445071917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131480925346304926296714611 197221388019457389445071917)
            ·
              refine ⟨73958020507296521041901969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 197221388019457389445071917 73958020507296521041901969)
              ·
                refine ⟨55468515380472390781426477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73958020507296521041901969 55468515380472390781426477)
                ·
                  refine ⟨20800693267677146543034929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55468515380472390781426477 20800693267677146543034929)
                  ·
                    refine ⟨15600519950757859907276197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20800693267677146543034929 15600519950757859907276197)
                    ·
                      refine ⟨2925097490767098732614287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15600519950757859907276197 2925097490767098732614287)
                      ·
                        rfl

theorem cell23_5696607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_5696607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5696607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5696607 prefixEnd_5696607 := by exact prefixLift 5696607
  have htrace : WordTrace (prefixWord ++ tailWord_5696607) baseStart_5696607 baseEnd_5696607 := by
    simpa [prefixWord, tailWord_5696607, baseEnd_5696607] using wordTrace_append hprefix tailTrace_5696607
  have hstable : (prefixWord ++ tailWord_5696607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5696607).length < 2 ^ (prefixWord ++ tailWord_5696607).sum := by decide
  have hdescent : baseEnd_5696607 < baseStart_5696607 := by decide
  rcases family_descends (prefixWord ++ tailWord_5696607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5696611 : List Nat := [1, 1, 1, 5, 1, 1, 1, 5, 3, 2, 2]
def baseStart_5696611 : Nat := 118140960795 + 5696611 * 2 ^ 59
def prefixEnd_5696611 : Nat := 4983230072969 + 3 ^ 40 * 5696611 * 2
def baseEnd_5696611 : Nat := 2925099544689716716964269

theorem tailTrace_5696611 : CollatzResearch.WordTrace tailWord_5696611 prefixEnd_5696611 2925099544689716716964269 := by
  unfold tailWord_5696611
  simp only [CollatzResearch.WordTrace]
  refine ⟨207772472365158725547089687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138514981576772483698059791 207772472365158725547089687)
  ·
    refine ⟨311658708547738088320634531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207772472365158725547089687 311658708547738088320634531)
    ·
      refine ⟨467488062821607132480951797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311658708547738088320634531 467488062821607132480951797)
      ·
        refine ⟨43827005889525668670089231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 467488062821607132480951797 43827005889525668670089231)
        ·
          refine ⟨65740508834288503005133847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43827005889525668670089231 65740508834288503005133847)
          ·
            refine ⟨98610763251432754507700771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65740508834288503005133847 98610763251432754507700771)
            ·
              refine ⟨147916144877149131761551157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98610763251432754507700771 147916144877149131761551157)
              ·
                refine ⟨13867138582232731102645421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 147916144877149131761551157 13867138582232731102645421)
                ·
                  refine ⟨5200176968337274163492033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13867138582232731102645421 5200176968337274163492033)
                  ·
                    refine ⟨3900132726252955622619025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5200176968337274163492033 3900132726252955622619025)
                    ·
                      refine ⟨2925099544689716716964269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3900132726252955622619025 2925099544689716716964269)
                      ·
                        rfl

theorem cell23_5696611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5, 3, 2, 2].length) (baseStart_5696611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5696611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5696611 prefixEnd_5696611 := by exact prefixLift 5696611
  have htrace : WordTrace (prefixWord ++ tailWord_5696611) baseStart_5696611 baseEnd_5696611 := by
    simpa [prefixWord, tailWord_5696611, baseEnd_5696611] using wordTrace_append hprefix tailTrace_5696611
  have hstable : (prefixWord ++ tailWord_5696611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5696611).length < 2 ^ (prefixWord ++ tailWord_5696611).sum := by decide
  have hdescent : baseEnd_5696611 < baseStart_5696611 := by decide
  rcases family_descends (prefixWord ++ tailWord_5696611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5696617 : List Nat := [1, 2, 1, 1, 1, 6, 3, 8]
def baseStart_5696617 : Nat := 118140960795 + 5696617 * 2 ^ 59
def prefixEnd_5696617 : Nat := 4983230072969 + 3 ^ 40 * 5696617 * 2
def baseEnd_5696617 : Nat := 108337134280505321981083

theorem tailTrace_5696617 : CollatzResearch.WordTrace tailWord_5696617 prefixEnd_5696617 108337134280505321981083 := by
  unfold tailWord_5696617
  simp only [CollatzResearch.WordTrace]
  refine ⟨207772691203136988571808105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138515127468757992381205403 207772691203136988571808105)
  ·
    refine ⟨155829518402352741428856079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207772691203136988571808105 155829518402352741428856079)
    ·
      refine ⟨233744277603529112143284119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155829518402352741428856079 233744277603529112143284119)
      ·
        refine ⟨350616416405293668214926179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233744277603529112143284119 350616416405293668214926179)
        ·
          refine ⟨525924624607940502322389269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350616416405293668214926179 525924624607940502322389269)
          ·
            refine ⟨24652716778497211046361997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 525924624607940502322389269 24652716778497211046361997)
            ·
              refine ⟨9244768791936454142385749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24652716778497211046361997 9244768791936454142385749)
              ·
                refine ⟨108337134280505321981083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9244768791936454142385749 108337134280505321981083)
                ·
                  rfl

theorem cell23_5696617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 8].length) (baseStart_5696617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5696617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5696617 prefixEnd_5696617 := by exact prefixLift 5696617
  have htrace : WordTrace (prefixWord ++ tailWord_5696617) baseStart_5696617 baseEnd_5696617 := by
    simpa [prefixWord, tailWord_5696617, baseEnd_5696617] using wordTrace_append hprefix tailTrace_5696617
  have hstable : (prefixWord ++ tailWord_5696617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5696617).length < 2 ^ (prefixWord ++ tailWord_5696617).sum := by decide
  have hdescent : baseEnd_5696617 < baseStart_5696617 := by decide
  rcases family_descends (prefixWord ++ tailWord_5696617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5696621 : List Nat := [1, 5, 1, 1, 2, 2, 2, 3, 2, 4]
def baseStart_5696621 : Nat := 118140960795 + 5696621 * 2 ^ 59
def prefixEnd_5696621 : Nat := 4983230072969 + 3 ^ 40 * 5696621 * 2
def baseEnd_5696621 : Nat := 975034893165420559279741

theorem tailTrace_5696621 : CollatzResearch.WordTrace tailWord_5696621 prefixEnd_5696621 975034893165420559279741 := by
  unfold tailWord_5696621
  simp only [CollatzResearch.WordTrace]
  refine ⟨207772837095122497254953717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138515224730081664836635811 207772837095122497254953717)
  ·
    refine ⟨19478703477667734117651911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 207772837095122497254953717 19478703477667734117651911)
    ·
      refine ⟨29218055216501601176477867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19478703477667734117651911 29218055216501601176477867)
      ·
        refine ⟨43827082824752401764716801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29218055216501601176477867 43827082824752401764716801)
        ·
          refine ⟨32870312118564301323537601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43827082824752401764716801 32870312118564301323537601)
          ·
            refine ⟨24652734088923225992653201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32870312118564301323537601 24652734088923225992653201)
            ·
              refine ⟨18489550566692419494489901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24652734088923225992653201 18489550566692419494489901)
              ·
                refine ⟨6933581462509657310433713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18489550566692419494489901 6933581462509657310433713)
                ·
                  refine ⟨5200186096882242982825285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6933581462509657310433713 5200186096882242982825285)
                  ·
                    refine ⟨975034893165420559279741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5200186096882242982825285 975034893165420559279741)
                    ·
                      rfl

theorem cell23_5696621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_5696621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5696621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5696621 prefixEnd_5696621 := by exact prefixLift 5696621
  have htrace : WordTrace (prefixWord ++ tailWord_5696621) baseStart_5696621 baseEnd_5696621 := by
    simpa [prefixWord, tailWord_5696621, baseEnd_5696621] using wordTrace_append hprefix tailTrace_5696621
  have hstable : (prefixWord ++ tailWord_5696621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5696621).length < 2 ^ (prefixWord ++ tailWord_5696621).sum := by decide
  have hdescent : baseEnd_5696621 < baseStart_5696621 := by decide
  rcases family_descends (prefixWord ++ tailWord_5696621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5696624 : List Nat := [2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 4]
def baseStart_5696624 : Nat := 118140960795 + 5696624 * 2 ^ 59
def prefixEnd_5696624 : Nat := 4983230072969 + 3 ^ 40 * 5696624 * 2
def baseEnd_5696624 : Nat := 2925106219938225166101709

theorem tailTrace_5696624 : CollatzResearch.WordTrace tailWord_5696624 prefixEnd_5696624 2925106219938225166101709 := by
  unfold tailWord_5696624
  simp only [CollatzResearch.WordTrace]
  refine ⟨103886473257055814383656463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138515297676074419178208617 103886473257055814383656463)
  ·
    refine ⟨155829709885583721575484695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103886473257055814383656463 155829709885583721575484695)
    ·
      refine ⟨233744564828375582363227043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155829709885583721575484695 233744564828375582363227043)
      ·
        refine ⟨350616847242563373544840565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233744564828375582363227043 350616847242563373544840565)
        ·
          refine ⟨32870329428990316269828803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 350616847242563373544840565 32870329428990316269828803)
          ·
            refine ⟨49305494143485474404743205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32870329428990316269828803 49305494143485474404743205)
            ·
              refine ⟨9244780151903526450889351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49305494143485474404743205 9244780151903526450889351)
              ·
                refine ⟨13867170227855289676334027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9244780151903526450889351 13867170227855289676334027)
                ·
                  refine ⟨20800755341782934514501041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13867170227855289676334027 20800755341782934514501041)
                  ·
                    refine ⟨15600566506337200885875781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20800755341782934514501041 15600566506337200885875781)
                    ·
                      refine ⟨2925106219938225166101709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15600566506337200885875781 2925106219938225166101709)
                      ·
                        rfl

theorem cell23_5696624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 4].length) (baseStart_5696624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5696624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5696624 prefixEnd_5696624 := by exact prefixLift 5696624
  have htrace : WordTrace (prefixWord ++ tailWord_5696624) baseStart_5696624 baseEnd_5696624 := by
    simpa [prefixWord, tailWord_5696624, baseEnd_5696624] using wordTrace_append hprefix tailTrace_5696624
  have hstable : (prefixWord ++ tailWord_5696624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5696624).length < 2 ^ (prefixWord ++ tailWord_5696624).sum := by decide
  have hdescent : baseEnd_5696624 < baseStart_5696624 := by decide
  rcases family_descends (prefixWord ++ tailWord_5696624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5696645 : List Nat := [1, 3, 1, 1, 7, 1, 2, 1, 1, 1, 4]
def baseStart_5696645 : Nat := 118140960795 + 5696645 * 2 ^ 59
def prefixEnd_5696645 : Nat := 4983230072969 + 3 ^ 40 * 5696645 * 2
def baseEnd_5696645 : Nat := 2925117003031969583939113

theorem tailTrace_5696645 : CollatzResearch.WordTrace tailWord_5696645 prefixEnd_5696645 2925117003031969583939113 := by
  unfold tailWord_5696645
  simp only [CollatzResearch.WordTrace]
  refine ⟨207773712447035549353827389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138515808298023699569218259 207773712447035549353827389)
  ·
    refine ⟨77915142167638331007685271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207773712447035549353827389 77915142167638331007685271)
    ·
      refine ⟨116872713251457496511527907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77915142167638331007685271 116872713251457496511527907)
      ·
        refine ⟨175309069877186244767291861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116872713251457496511527907 175309069877186244767291861)
        ·
          refine ⟨4108806325246552611733403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 175309069877186244767291861 4108806325246552611733403)
          ·
            refine ⟨6163209487869828917600105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4108806325246552611733403 6163209487869828917600105)
            ·
              refine ⟨4622407115902371688200079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6163209487869828917600105 4622407115902371688200079)
              ·
                refine ⟨6933610673853557532300119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4622407115902371688200079 6933610673853557532300119)
                ·
                  refine ⟨10400416010780336298450179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6933610673853557532300119 10400416010780336298450179)
                  ·
                    refine ⟨15600624016170504447675269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10400416010780336298450179 15600624016170504447675269)
                    ·
                      refine ⟨2925117003031969583939113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15600624016170504447675269 2925117003031969583939113)
                      ·
                        rfl

theorem cell23_5696645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 1, 1, 1, 4].length) (baseStart_5696645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5696645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5696645 prefixEnd_5696645 := by exact prefixLift 5696645
  have htrace : WordTrace (prefixWord ++ tailWord_5696645) baseStart_5696645 baseEnd_5696645 := by
    simpa [prefixWord, tailWord_5696645, baseEnd_5696645] using wordTrace_append hprefix tailTrace_5696645
  have hstable : (prefixWord ++ tailWord_5696645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5696645).length < 2 ^ (prefixWord ++ tailWord_5696645).sum := by decide
  have hdescent : baseEnd_5696645 < baseStart_5696645 := by decide
  rcases family_descends (prefixWord ++ tailWord_5696645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5696648 : List Nat := [2, 1, 3, 4, 2, 1, 1, 3, 1, 2, 3]
def baseStart_5696648 : Nat := 118140960795 + 5696648 * 2 ^ 59
def prefixEnd_5696648 : Nat := 4983230072969 + 3 ^ 40 * 5696648 * 2
def baseEnd_5696648 : Nat := 2925118543473933072201599

theorem tailTrace_5696648 : CollatzResearch.WordTrace tailWord_5696648 prefixEnd_5696648 2925118543473933072201599 := by
  unfold tailWord_5696648
  simp only [CollatzResearch.WordTrace]
  refine ⟨103886910933012340433093299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138515881244016453910791065 103886910933012340433093299)
  ·
    refine ⟨155830366399518510649639949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103886910933012340433093299 155830366399518510649639949)
    ·
      refine ⟨58436387399819441493614981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155830366399518510649639949 58436387399819441493614981)
      ·
        refine ⟨10956822637466145280052809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58436387399819441493614981 10956822637466145280052809)
        ·
          refine ⟨8217616978099608960039607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10956822637466145280052809 8217616978099608960039607)
          ·
            refine ⟨12326425467149413440059411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8217616978099608960039607 12326425467149413440059411)
            ·
              refine ⟨18489638200724120160089117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12326425467149413440059411 18489638200724120160089117)
              ·
                refine ⟨6933614325271545060033419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18489638200724120160089117 6933614325271545060033419)
                ·
                  refine ⟨10400421487907317590050129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6933614325271545060033419 10400421487907317590050129)
                  ·
                    refine ⟨7800316115930488192537597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10400421487907317590050129 7800316115930488192537597)
                    ·
                      refine ⟨2925118543473933072201599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7800316115930488192537597 2925118543473933072201599)
                      ·
                        rfl

theorem cell23_5696648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_5696648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5696648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5696648 prefixEnd_5696648 := by exact prefixLift 5696648
  have htrace : WordTrace (prefixWord ++ tailWord_5696648) baseStart_5696648 baseEnd_5696648 := by
    simpa [prefixWord, tailWord_5696648, baseEnd_5696648] using wordTrace_append hprefix tailTrace_5696648
  have hstable : (prefixWord ++ tailWord_5696648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5696648).length < 2 ^ (prefixWord ++ tailWord_5696648).sum := by decide
  have hdescent : baseEnd_5696648 < baseStart_5696648 := by decide
  rcases family_descends (prefixWord ++ tailWord_5696648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5696661 : List Nat := [1, 3, 2, 1, 1, 1, 2, 6, 2, 1, 3]
def baseStart_5696661 : Nat := 118140960795 + 5696661 * 2 ^ 59
def prefixEnd_5696661 : Nat := 4983230072969 + 3 ^ 40 * 5696661 * 2
def baseEnd_5696661 : Nat := 2925125218722441521339039

theorem tailTrace_5696661 : CollatzResearch.WordTrace tailWord_5696661 prefixEnd_5696661 2925125218722441521339039 := by
  unfold tailWord_5696661
  simp only [CollatzResearch.WordTrace]
  refine ⟨207774296014977584086409837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138516197343318389390939891 207774296014977584086409837)
  ·
    refine ⟨77915361005616594032403689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207774296014977584086409837 77915361005616594032403689)
    ·
      refine ⟨58436520754212445524302767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77915361005616594032403689 58436520754212445524302767)
      ·
        refine ⟨87654781131318668286454151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58436520754212445524302767 87654781131318668286454151)
        ·
          refine ⟨131482171696978002429681227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87654781131318668286454151 131482171696978002429681227)
          ·
            refine ⟨197223257545467003644521841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131482171696978002429681227 197223257545467003644521841)
            ·
              refine ⟨147917443159100252733391381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197223257545467003644521841 147917443159100252733391381)
              ·
                refine ⟨6933630148082824346877721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 147917443159100252733391381 6933630148082824346877721)
                ·
                  refine ⟨5200222611062118260158291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6933630148082824346877721 5200222611062118260158291)
                  ·
                    refine ⟨7800333916593177390237437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5200222611062118260158291 7800333916593177390237437)
                    ·
                      refine ⟨2925125218722441521339039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7800333916593177390237437 2925125218722441521339039)
                      ·
                        rfl

theorem cell23_5696661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 6, 2, 1, 3].length) (baseStart_5696661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5696661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5696661 prefixEnd_5696661 := by exact prefixLift 5696661
  have htrace : WordTrace (prefixWord ++ tailWord_5696661) baseStart_5696661 baseEnd_5696661 := by
    simpa [prefixWord, tailWord_5696661, baseEnd_5696661] using wordTrace_append hprefix tailTrace_5696661
  have hstable : (prefixWord ++ tailWord_5696661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5696661).length < 2 ^ (prefixWord ++ tailWord_5696661).sum := by decide
  have hdescent : baseEnd_5696661 < baseStart_5696661 := by decide
  rcases family_descends (prefixWord ++ tailWord_5696661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5696701 : List Nat := [1, 4, 1, 2, 1, 1, 2, 4, 1, 4, 2]
def baseStart_5696701 : Nat := 118140960795 + 5696701 * 2 ^ 59
def prefixEnd_5696701 : Nat := 4983230072969 + 3 ^ 40 * 5696701 * 2
def baseEnd_5696701 : Nat := 2925145757948621364838855

theorem tailTrace_5696701 : CollatzResearch.WordTrace tailWord_5696701 prefixEnd_5696701 2925145757948621364838855 := by
  unfold tailWord_5696701
  simp only [CollatzResearch.WordTrace]
  refine ⟨207775754934832670917865957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138517169956555113945243971 207775754934832670917865957)
  ·
    refine ⟨38957954050281125797099867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 207775754934832670917865957 38957954050281125797099867)
    ·
      refine ⟨58436931075421688695649801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38957954050281125797099867 58436931075421688695649801)
      ·
        refine ⟨43827698306566266521737351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58436931075421688695649801 43827698306566266521737351)
        ·
          refine ⟨65741547459849399782606027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43827698306566266521737351 65741547459849399782606027)
          ·
            refine ⟨98612321189774099673909041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65741547459849399782606027 98612321189774099673909041)
            ·
              refine ⟨73959240892330574755431781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98612321189774099673909041 73959240892330574755431781)
              ·
                refine ⟨13867357667311982766643459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73959240892330574755431781 13867357667311982766643459)
                ·
                  refine ⟨20801036500967974149965189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13867357667311982766643459 20801036500967974149965189)
                  ·
                    refine ⟨3900194343931495153118473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20801036500967974149965189 3900194343931495153118473)
                    ·
                      refine ⟨2925145757948621364838855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3900194343931495153118473 2925145757948621364838855)
                      ·
                        rfl

theorem cell23_5696701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4, 1, 4, 2].length) (baseStart_5696701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5696701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5696701 prefixEnd_5696701 := by exact prefixLift 5696701
  have htrace : WordTrace (prefixWord ++ tailWord_5696701) baseStart_5696701 baseEnd_5696701 := by
    simpa [prefixWord, tailWord_5696701, baseEnd_5696701] using wordTrace_append hprefix tailTrace_5696701
  have hstable : (prefixWord ++ tailWord_5696701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5696701).length < 2 ^ (prefixWord ++ tailWord_5696701).sum := by decide
  have hdescent : baseEnd_5696701 < baseStart_5696701 := by decide
  rcases family_descends (prefixWord ++ tailWord_5696701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5696705 : List Nat := [1, 2, 6, 1, 1, 1, 2, 3, 1, 3, 2]
def baseStart_5696705 : Nat := 118140960795 + 5696705 * 2 ^ 59
def prefixEnd_5696705 : Nat := 4983230072969 + 3 ^ 40 * 5696705 * 2
def baseEnd_5696705 : Nat := 2925147811871239349188837

theorem tailTrace_5696705 : CollatzResearch.WordTrace tailWord_5696705 prefixEnd_5696705 2925147811871239349188837 := by
  unfold tailWord_5696705
  simp only [CollatzResearch.WordTrace]
  refine ⟨207775900826818179601011569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138517267217878786400674379 207775900826818179601011569)
  ·
    refine ⟨155831925620113634700758677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207775900826818179601011569 155831925620113634700758677)
    ·
      refine ⟨7304621513442826626598063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 155831925620113634700758677 7304621513442826626598063)
      ·
        refine ⟨10956932270164239939897095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7304621513442826626598063 10956932270164239939897095)
        ·
          refine ⟨16435398405246359909845643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10956932270164239939897095 16435398405246359909845643)
          ·
            refine ⟨24653097607869539864768465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16435398405246359909845643 24653097607869539864768465)
            ·
              refine ⟨18489823205902154898576349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24653097607869539864768465 18489823205902154898576349)
              ·
                refine ⟨6933683702213308086966131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18489823205902154898576349 6933683702213308086966131)
                ·
                  refine ⟨10400525553319962130449197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6933683702213308086966131 10400525553319962130449197)
                  ·
                    refine ⟨3900197082494985798918449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10400525553319962130449197 3900197082494985798918449)
                    ·
                      refine ⟨2925147811871239349188837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3900197082494985798918449 2925147811871239349188837)
                      ·
                        rfl

theorem cell23_5696705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_5696705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5696705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5696705 prefixEnd_5696705 := by exact prefixLift 5696705
  have htrace : WordTrace (prefixWord ++ tailWord_5696705) baseStart_5696705 baseEnd_5696705 := by
    simpa [prefixWord, tailWord_5696705, baseEnd_5696705] using wordTrace_append hprefix tailTrace_5696705
  have hstable : (prefixWord ++ tailWord_5696705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5696705).length < 2 ^ (prefixWord ++ tailWord_5696705).sum := by decide
  have hdescent : baseEnd_5696705 < baseStart_5696705 := by decide
  rcases family_descends (prefixWord ++ tailWord_5696705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5696735 : List Nat := [1, 1, 2, 3, 2, 1, 6, 1, 2, 2, 2]
def baseStart_5696735 : Nat := 118140960795 + 5696735 * 2 ^ 59
def prefixEnd_5696735 : Nat := 4983230072969 + 3 ^ 40 * 5696735 * 2
def baseEnd_5696735 : Nat := 2925163216290874231813699

theorem tailTrace_5696735 : CollatzResearch.WordTrace tailWord_5696735 prefixEnd_5696735 2925163216290874231813699 := by
  unfold tailWord_5696735
  simp only [CollatzResearch.WordTrace]
  refine ⟨207776995016709494724603659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138517996677806329816402439 207776995016709494724603659)
  ·
    refine ⟨311665492525064242086905489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207776995016709494724603659 311665492525064242086905489)
    ·
      refine ⟨233749119393798181565179117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311665492525064242086905489 233749119393798181565179117)
      ·
        refine ⟨87655919772674318086942169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 233749119393798181565179117 87655919772674318086942169)
        ·
          refine ⟨65741939829505738565206627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87655919772674318086942169 65741939829505738565206627)
          ·
            refine ⟨98612909744258607847809941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65741939829505738565206627 98612909744258607847809941)
            ·
              refine ⟨4622480144262122242866091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 98612909744258607847809941 4622480144262122242866091)
              ·
                refine ⟨6933720216393183364299137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4622480144262122242866091 6933720216393183364299137)
                ·
                  refine ⟨5200290162294887523224353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6933720216393183364299137 5200290162294887523224353)
                  ·
                    refine ⟨3900217621721165642418265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5200290162294887523224353 3900217621721165642418265)
                    ·
                      refine ⟨2925163216290874231813699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3900217621721165642418265 2925163216290874231813699)
                      ·
                        rfl

theorem cell23_5696735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 1, 2, 2, 2].length) (baseStart_5696735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5696735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5696735 prefixEnd_5696735 := by exact prefixLift 5696735
  have htrace : WordTrace (prefixWord ++ tailWord_5696735) baseStart_5696735 baseEnd_5696735 := by
    simpa [prefixWord, tailWord_5696735, baseEnd_5696735] using wordTrace_append hprefix tailTrace_5696735
  have hstable : (prefixWord ++ tailWord_5696735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5696735).length < 2 ^ (prefixWord ++ tailWord_5696735).sum := by decide
  have hdescent : baseEnd_5696735 < baseStart_5696735 := by decide
  rcases family_descends (prefixWord ++ tailWord_5696735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5696756 : List Nat := [2, 6, 1, 2, 1, 1, 3, 1, 1, 3, 2]
def baseStart_5696756 : Nat := 118140960795 + 5696756 * 2 ^ 59
def prefixEnd_5696756 : Nat := 4983230072969 + 3 ^ 40 * 5696756 * 2
def baseEnd_5696756 : Nat := 2925173999384618649651103

theorem tailTrace_5696756 : CollatzResearch.WordTrace tailWord_5696756 prefixEnd_5696756 2925173999384618649651103 := by
  unfold tailWord_5696756
  simp only [CollatzResearch.WordTrace]
  refine ⟨103888880474816707655559061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138518507299755610207412081 103888880474816707655559061)
  ·
    refine ⟨4869791272257033171354331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 103888880474816707655559061 4869791272257033171354331)
    ·
      refine ⟨7304686908385549757031497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4869791272257033171354331 7304686908385549757031497)
      ·
        refine ⟨5478515181289162317773623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7304686908385549757031497 5478515181289162317773623)
        ·
          refine ⟨8217772771933743476660435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5478515181289162317773623 8217772771933743476660435)
          ·
            refine ⟨12326659157900615214990653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8217772771933743476660435 12326659157900615214990653)
            ·
              refine ⟨4622497184212730705621495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12326659157900615214990653 4622497184212730705621495)
              ·
                refine ⟨6933745776319096058432243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4622497184212730705621495 6933745776319096058432243)
                ·
                  refine ⟨10400618664478644087648365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6933745776319096058432243 10400618664478644087648365)
                  ·
                    refine ⟨3900231999179491532868137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10400618664478644087648365 3900231999179491532868137)
                    ·
                      refine ⟨2925173999384618649651103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3900231999179491532868137 2925173999384618649651103)
                      ·
                        rfl

theorem cell23_5696756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_5696756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5696756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5696756 prefixEnd_5696756 := by exact prefixLift 5696756
  have htrace : WordTrace (prefixWord ++ tailWord_5696756) baseStart_5696756 baseEnd_5696756 := by
    simpa [prefixWord, tailWord_5696756, baseEnd_5696756] using wordTrace_append hprefix tailTrace_5696756
  have hstable : (prefixWord ++ tailWord_5696756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5696756).length < 2 ^ (prefixWord ++ tailWord_5696756).sum := by decide
  have hdescent : baseEnd_5696756 < baseStart_5696756 := by decide
  rcases family_descends (prefixWord ++ tailWord_5696756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5696808 : List Nat := [2, 1, 5, 1, 2, 1, 3, 1, 2, 1, 4]
def baseStart_5696808 : Nat := 118140960795 + 5696808 * 2 ^ 59
def prefixEnd_5696808 : Nat := 4983230072969 + 3 ^ 40 * 5696808 * 2
def baseEnd_5696808 : Nat := 2925200700378652446200863

theorem tailTrace_5696808 : CollatzResearch.WordTrace tailWord_5696808 prefixEnd_5696808 2925200700378652446200863 := by
  unfold tailWord_5696808
  simp only [CollatzResearch.WordTrace]
  refine ⟨103889828772722514096005539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138519771696963352128007385 103889828772722514096005539)
  ·
    refine ⟨155834743159083771144008309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103889828772722514096005539 155834743159083771144008309)
    ·
      refine ⟨14609507171164103544750779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 155834743159083771144008309 14609507171164103544750779)
      ·
        refine ⟨21914260756746155317126169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14609507171164103544750779 21914260756746155317126169)
        ·
          refine ⟨16435695567559616487844627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21914260756746155317126169 16435695567559616487844627)
          ·
            refine ⟨24653543351339424731766941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16435695567559616487844627 24653543351339424731766941)
            ·
              refine ⟨9245078756752284274412603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24653543351339424731766941 9245078756752284274412603)
              ·
                refine ⟨13867618135128426411618905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9245078756752284274412603 13867618135128426411618905)
                ·
                  refine ⟨10400713601346319808714179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13867618135128426411618905 10400713601346319808714179)
                  ·
                    refine ⟨15601070402019479713071269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10400713601346319808714179 15601070402019479713071269)
                    ·
                      refine ⟨2925200700378652446200863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15601070402019479713071269 2925200700378652446200863)
                      ·
                        rfl

theorem cell23_5696808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_5696808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5696808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5696808 prefixEnd_5696808 := by exact prefixLift 5696808
  have htrace : WordTrace (prefixWord ++ tailWord_5696808) baseStart_5696808 baseEnd_5696808 := by
    simpa [prefixWord, tailWord_5696808, baseEnd_5696808] using wordTrace_append hprefix tailTrace_5696808
  have hstable : (prefixWord ++ tailWord_5696808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5696808).length < 2 ^ (prefixWord ++ tailWord_5696808).sum := by decide
  have hdescent : baseEnd_5696808 < baseStart_5696808 := by decide
  rcases family_descends (prefixWord ++ tailWord_5696808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5696831 : List Nat := [1, 1, 2, 2, 4, 2, 3, 2, 6]
def baseStart_5696831 : Nat := 118140960795 + 5696831 * 2 ^ 59
def prefixEnd_5696831 : Nat := 4983230072969 + 3 ^ 40 * 5696831 * 2
def baseEnd_5696831 : Nat := 325023612270411761801473

theorem tailTrace_5696831 : CollatzResearch.WordTrace tailWord_5696831 prefixEnd_5696831 325023612270411761801473 := by
  unfold tailWord_5696831
  simp only [CollatzResearch.WordTrace]
  refine ⟨207780496424361703120098347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138520330949574468746732231 207780496424361703120098347)
  ·
    refine ⟨311670744636542554680147521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207780496424361703120098347 311670744636542554680147521)
    ·
      refine ⟨233753058477406916010110641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311670744636542554680147521 233753058477406916010110641)
      ·
        refine ⟨175314793858055187007582981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233753058477406916010110641 175314793858055187007582981)
        ·
          refine ⟨32871523848385347563921809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 175314793858055187007582981 32871523848385347563921809)
          ·
            refine ⟨24653642886289010672941357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32871523848385347563921809 24653642886289010672941357)
            ·
              refine ⟨9245116082358379002353009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24653642886289010672941357 9245116082358379002353009)
              ·
                refine ⟨6933837061768784251764757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9245116082358379002353009 6933837061768784251764757)
                ·
                  refine ⟨325023612270411761801473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6933837061768784251764757 325023612270411761801473)
                  ·
                    rfl

theorem cell23_5696831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 2, 6].length) (baseStart_5696831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5696831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5696831 prefixEnd_5696831 := by exact prefixLift 5696831
  have htrace : WordTrace (prefixWord ++ tailWord_5696831) baseStart_5696831 baseEnd_5696831 := by
    simpa [prefixWord, tailWord_5696831, baseEnd_5696831] using wordTrace_append hprefix tailTrace_5696831
  have hstable : (prefixWord ++ tailWord_5696831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5696831).length < 2 ^ (prefixWord ++ tailWord_5696831).sum := by decide
  have hdescent : baseEnd_5696831 < baseStart_5696831 := by decide
  rcases family_descends (prefixWord ++ tailWord_5696831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5696851 : List Nat := [1, 1, 1, 2, 1, 1, 5, 1, 3, 5, 2]
def baseStart_5696851 : Nat := 118140960795 + 5696851 * 2 ^ 59
def prefixEnd_5696851 : Nat := 4983230072969 + 3 ^ 40 * 5696851 * 2
def baseEnd_5696851 : Nat := 2925222780046795777963165

theorem tailTrace_5696851 : CollatzResearch.WordTrace tailWord_5696851 prefixEnd_5696851 2925222780046795777963165 := by
  unfold tailWord_5696851
  simp only [CollatzResearch.WordTrace]
  refine ⟨207781225884289246535826407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138520817256192831023884271 207781225884289246535826407)
  ·
    refine ⟨311671838826433869803739611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207781225884289246535826407 311671838826433869803739611)
    ·
      refine ⟨467507758239650804705609417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311671838826433869803739611 467507758239650804705609417)
      ·
        refine ⟨350630818679738103529207063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 467507758239650804705609417 350630818679738103529207063)
        ·
          refine ⟨525946228019607155293810595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350630818679738103529207063 525946228019607155293810595)
          ·
            refine ⟨788919342029410732940715893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 525946228019607155293810595 788919342029410732940715893)
            ·
              refine ⟨73961188315257256213192115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 788919342029410732940715893 73961188315257256213192115)
              ·
                refine ⟨110941782472885884319788173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73961188315257256213192115 110941782472885884319788173)
                ·
                  refine ⟨41603168427332206619920565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110941782472885884319788173 41603168427332206619920565)
                  ·
                    refine ⟨3900297040062394370617553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41603168427332206619920565 3900297040062394370617553)
                    ·
                      refine ⟨2925222780046795777963165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3900297040062394370617553 2925222780046795777963165)
                      ·
                        rfl

theorem cell23_5696851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 5, 2].length) (baseStart_5696851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5696851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5696851 prefixEnd_5696851 := by exact prefixLift 5696851
  have htrace : WordTrace (prefixWord ++ tailWord_5696851) baseStart_5696851 baseEnd_5696851 := by
    simpa [prefixWord, tailWord_5696851, baseEnd_5696851] using wordTrace_append hprefix tailTrace_5696851
  have hstable : (prefixWord ++ tailWord_5696851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5696851).length < 2 ^ (prefixWord ++ tailWord_5696851).sum := by decide
  have hdescent : baseEnd_5696851 < baseStart_5696851 := by decide
  rcases family_descends (prefixWord ++ tailWord_5696851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5696858 : List Nat := [3, 1, 1, 2, 1, 2, 4, 2, 3, 1, 3]
def baseStart_5696858 : Nat := 118140960795 + 5696858 * 2 ^ 59
def prefixEnd_5696858 : Nat := 4983230072969 + 3 ^ 40 * 5696858 * 2
def baseEnd_5696858 : Nat := 2925226374411377250575633

theorem tailTrace_5696858 : CollatzResearch.WordTrace tailWord_5696858 prefixEnd_5696858 2925226374411377250575633 := by
  unfold tailWord_5696858
  simp only [CollatzResearch.WordTrace]
  refine ⟨51945370298815971682832807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138520987463509257820887485 51945370298815971682832807)
  ·
    refine ⟨77918055448223957524249211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51945370298815971682832807 77918055448223957524249211)
    ·
      refine ⟨116877083172335936286373817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77918055448223957524249211 116877083172335936286373817)
      ·
        refine ⟨87657812379251952214780363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116877083172335936286373817 87657812379251952214780363)
        ·
          refine ⟨131486718568877928322170545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87657812379251952214780363 131486718568877928322170545)
          ·
            refine ⟨98615038926658446241627909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131486718568877928322170545 98615038926658446241627909)
            ·
              refine ⟨18490319798748458670305233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98615038926658446241627909 18490319798748458670305233)
              ·
                refine ⟨13867739849061344002728925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18490319798748458670305233 13867739849061344002728925)
                ·
                  refine ⟨5200402443398004001023347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13867739849061344002728925 5200402443398004001023347)
                  ·
                    refine ⟨7800603665097006001535021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5200402443398004001023347 7800603665097006001535021)
                    ·
                      refine ⟨2925226374411377250575633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7800603665097006001535021 2925226374411377250575633)
                      ·
                        rfl

theorem cell23_5696858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2, 3, 1, 3].length) (baseStart_5696858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5696858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5696858 prefixEnd_5696858 := by exact prefixLift 5696858
  have htrace : WordTrace (prefixWord ++ tailWord_5696858) baseStart_5696858 baseEnd_5696858 := by
    simpa [prefixWord, tailWord_5696858, baseEnd_5696858] using wordTrace_append hprefix tailTrace_5696858
  have hstable : (prefixWord ++ tailWord_5696858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5696858).length < 2 ^ (prefixWord ++ tailWord_5696858).sum := by decide
  have hdescent : baseEnd_5696858 < baseStart_5696858 := by decide
  rcases family_descends (prefixWord ++ tailWord_5696858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5696868 : List Nat := [2, 3, 1, 1, 3, 2, 2, 1, 1, 5, 2]
def baseStart_5696868 : Nat := 118140960795 + 5696868 * 2 ^ 59
def prefixEnd_5696868 : Nat := 4983230072969 + 3 ^ 40 * 5696868 * 2
def baseEnd_5696868 : Nat := 2925231509217922211450587

theorem tailTrace_5696868 : CollatzResearch.WordTrace tailWord_5696868 prefixEnd_5696868 2925231509217922211450587 := by
  unfold tailWord_5696868
  simp only [CollatzResearch.WordTrace]
  refine ⟨103890922962613829219597629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138521230616818438959463505 103890922962613829219597629)
  ·
    refine ⟨38959096110980185957349111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103890922962613829219597629 38959096110980185957349111)
    ·
      refine ⟨58438644166470278936023667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38959096110980185957349111 58438644166470278936023667)
      ·
        refine ⟨87657966249705418404035501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58438644166470278936023667 87657966249705418404035501)
        ·
          refine ⟨32871737343639531901513313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87657966249705418404035501 32871737343639531901513313)
          ·
            refine ⟨24653803007729648926134985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32871737343639531901513313 24653803007729648926134985)
            ·
              refine ⟨18490352255797236694601239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24653803007729648926134985 18490352255797236694601239)
              ·
                refine ⟨27735528383695855041901859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18490352255797236694601239 27735528383695855041901859)
                ·
                  refine ⟨41603292575543782562852789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27735528383695855041901859 41603292575543782562852789)
                  ·
                    refine ⟨3900308678957229615267449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41603292575543782562852789 3900308678957229615267449)
                    ·
                      refine ⟨2925231509217922211450587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3900308678957229615267449 2925231509217922211450587)
                      ·
                        rfl

theorem cell23_5696868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 1, 5, 2].length) (baseStart_5696868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5696868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5696868 prefixEnd_5696868 := by exact prefixLift 5696868
  have htrace : WordTrace (prefixWord ++ tailWord_5696868) baseStart_5696868 baseEnd_5696868 := by
    simpa [prefixWord, tailWord_5696868, baseEnd_5696868] using wordTrace_append hprefix tailTrace_5696868
  have hstable : (prefixWord ++ tailWord_5696868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5696868).length < 2 ^ (prefixWord ++ tailWord_5696868).sum := by decide
  have hdescent : baseEnd_5696868 < baseStart_5696868 := by decide
  rcases family_descends (prefixWord ++ tailWord_5696868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5696891 : List Nat := [1, 1, 1, 1, 1, 6, 1, 3, 4, 4]
def baseStart_5696891 : Nat := 118140960795 + 5696891 * 2 ^ 59
def prefixEnd_5696891 : Nat := 4983230072969 + 3 ^ 40 * 5696891 * 2
def baseEnd_5696891 : Nat := 975081106424325207154327

theorem tailTrace_5696891 : CollatzResearch.WordTrace tailWord_5696891 prefixEnd_5696891 975081106424325207154327 := by
  unfold tailWord_5696891
  simp only [CollatzResearch.WordTrace]
  refine ⟨207782684804144333367282527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138521789869429555578188351 207782684804144333367282527)
  ·
    refine ⟨311674027206216500050923791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207782684804144333367282527 311674027206216500050923791)
    ·
      refine ⟨467511040809324750076385687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311674027206216500050923791 467511040809324750076385687)
      ·
        refine ⟨701266561213987125114578531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 467511040809324750076385687 701266561213987125114578531)
        ·
          refine ⟨1051899841820980687671867797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 701266561213987125114578531 1051899841820980687671867797)
          ·
            refine ⟨49307805085358469734618803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1051899841820980687671867797 49307805085358469734618803)
            ·
              refine ⟨73961707628037704601928205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49307805085358469734618803 73961707628037704601928205)
              ·
                refine ⟨27735640360514139225723077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73961707628037704601928205 27735640360514139225723077)
                ·
                  refine ⟨5200432567596401104823077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27735640360514139225723077 5200432567596401104823077)
                  ·
                    refine ⟨975081106424325207154327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5200432567596401104823077 975081106424325207154327)
                    ·
                      rfl

theorem cell23_5696891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 4, 4].length) (baseStart_5696891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5696891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5696891 prefixEnd_5696891 := by exact prefixLift 5696891
  have htrace : WordTrace (prefixWord ++ tailWord_5696891) baseStart_5696891 baseEnd_5696891 := by
    simpa [prefixWord, tailWord_5696891, baseEnd_5696891] using wordTrace_append hprefix tailTrace_5696891
  have hstable : (prefixWord ++ tailWord_5696891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5696891).length < 2 ^ (prefixWord ++ tailWord_5696891).sum := by decide
  have hdescent : baseEnd_5696891 < baseStart_5696891 := by decide
  rcases family_descends (prefixWord ++ tailWord_5696891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5696892 : List Nat := [2, 2, 2, 1, 1, 1, 7, 2, 1, 1, 3]
def baseStart_5696892 : Nat := 118140960795 + 5696892 * 2 ^ 59
def prefixEnd_5696892 : Nat := 4983230072969 + 3 ^ 40 * 5696892 * 2
def baseEnd_5696892 : Nat := 2925243832753630117550477

theorem tailTrace_5696892 : CollatzResearch.WordTrace tailWord_5696892 prefixEnd_5696892 2925243832753630117550477 := by
  unfold tailWord_5696892
  simp only [CollatzResearch.WordTrace]
  refine ⟨103891360638570355269034465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138521814184760473692045953 103891360638570355269034465)
  ·
    refine ⟨77918520478927766451775849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103891360638570355269034465 77918520478927766451775849)
    ·
      refine ⟨58438890359195824838831887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77918520478927766451775849 58438890359195824838831887)
      ·
        refine ⟨87658335538793737258247831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58438890359195824838831887 87658335538793737258247831)
        ·
          refine ⟨131487503308190605887371747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87658335538793737258247831 131487503308190605887371747)
          ·
            refine ⟨197231254962285908831057621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131487503308190605887371747 197231254962285908831057621)
            ·
              refine ⟨4622607538178575988227913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 197231254962285908831057621 4622607538178575988227913)
              ·
                refine ⟨3466955653633931991170935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4622607538178575988227913 3466955653633931991170935)
                ·
                  refine ⟨5200433480450897986756403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3466955653633931991170935 5200433480450897986756403)
                  ·
                    refine ⟨7800650220676346980134605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5200433480450897986756403 7800650220676346980134605)
                    ·
                      refine ⟨2925243832753630117550477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7800650220676346980134605 2925243832753630117550477)
                      ·
                        rfl

theorem cell23_5696892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 2, 1, 1, 3].length) (baseStart_5696892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5696892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5696892 prefixEnd_5696892 := by exact prefixLift 5696892
  have htrace : WordTrace (prefixWord ++ tailWord_5696892) baseStart_5696892 baseEnd_5696892 := by
    simpa [prefixWord, tailWord_5696892, baseEnd_5696892] using wordTrace_append hprefix tailTrace_5696892
  have hstable : (prefixWord ++ tailWord_5696892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5696892).length < 2 ^ (prefixWord ++ tailWord_5696892).sum := by decide
  have hdescent : baseEnd_5696892 < baseStart_5696892 := by decide
  rcases family_descends (prefixWord ++ tailWord_5696892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5696901 : List Nat := [1, 3, 1, 1, 3, 1, 4, 2, 1, 1, 5]
def baseStart_5696901 : Nat := 118140960795 + 5696901 * 2 ^ 59
def prefixEnd_5696901 : Nat := 4983230072969 + 3 ^ 40 * 5696901 * 2
def baseEnd_5696901 : Nat := 2925248454079520582337935

theorem tailTrace_5696901 : CollatzResearch.WordTrace tailWord_5696901 prefixEnd_5696901 2925248454079520582337935 := by
  unfold tailWord_5696901
  simp only [CollatzResearch.WordTrace]
  refine ⟨207783049534108105075146557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138522033022738736716764371 207783049534108105075146557)
  ·
    refine ⟨77918643575290539403179959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207783049534108105075146557 77918643575290539403179959)
    ·
      refine ⟨116877965362935809104769939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77918643575290539403179959 116877965362935809104769939)
      ·
        refine ⟨175316948044403713657154909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116877965362935809104769939 175316948044403713657154909)
        ·
          refine ⟨65743855516651392621433091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175316948044403713657154909 65743855516651392621433091)
          ·
            refine ⟨98615783274977088932149637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65743855516651392621433091 98615783274977088932149637)
            ·
              refine ⟨18490459364058204174778057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98615783274977088932149637 18490459364058204174778057)
              ·
                refine ⟨13867844523043653131083543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18490459364058204174778057 13867844523043653131083543)
                ·
                  refine ⟨20801766784565479696625315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13867844523043653131083543 20801766784565479696625315)
                  ·
                    refine ⟨31202650176848219544937973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20801766784565479696625315 31202650176848219544937973)
                    ·
                      refine ⟨2925248454079520582337935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31202650176848219544937973 2925248454079520582337935)
                      ·
                        rfl

theorem cell23_5696901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2, 1, 1, 5].length) (baseStart_5696901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5696901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5696901 prefixEnd_5696901 := by exact prefixLift 5696901
  have htrace : WordTrace (prefixWord ++ tailWord_5696901) baseStart_5696901 baseEnd_5696901 := by
    simpa [prefixWord, tailWord_5696901, baseEnd_5696901] using wordTrace_append hprefix tailTrace_5696901
  have hstable : (prefixWord ++ tailWord_5696901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5696901).length < 2 ^ (prefixWord ++ tailWord_5696901).sum := by decide
  have hdescent : baseEnd_5696901 < baseStart_5696901 := by decide
  rcases family_descends (prefixWord ++ tailWord_5696901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5696908 : List Nat := [2, 2, 1, 2, 1, 3, 3, 3, 2, 4]
def baseStart_5696908 : Nat := 118140960795 + 5696908 * 2 ^ 59
def prefixEnd_5696908 : Nat := 4983230072969 + 3 ^ 40 * 5696908 * 2
def baseEnd_5696908 : Nat := 975084016148034018316801

theorem tailTrace_5696908 : CollatzResearch.WordTrace tailWord_5696908 prefixEnd_5696908 975084016148034018316801 := by
  unfold tailWord_5696908
  simp only [CollatzResearch.WordTrace]
  refine ⟨103891652422541372635325689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138522203230055163513767585 103891652422541372635325689)
  ·
    refine ⟨77918739316906029476494267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103891652422541372635325689 77918739316906029476494267)
    ·
      refine ⟨116878108975359044214741401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77918739316906029476494267 116878108975359044214741401)
      ·
        refine ⟨87658581731519283161056051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116878108975359044214741401 87658581731519283161056051)
        ·
          refine ⟨131487872597278924741584077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87658581731519283161056051 131487872597278924741584077)
          ·
            refine ⟨49307952223979596778094029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131487872597278924741584077 49307952223979596778094029)
            ·
              refine ⟨18490482083992348791785261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49307952223979596778094029 18490482083992348791785261)
              ·
                refine ⟨6933930781497130796919473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18490482083992348791785261 6933930781497130796919473)
                ·
                  refine ⟨5200448086122848097689605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6933930781497130796919473 5200448086122848097689605)
                  ·
                    refine ⟨975084016148034018316801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5200448086122848097689605 975084016148034018316801)
                    ·
                      rfl

theorem cell23_5696908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 3, 2, 4].length) (baseStart_5696908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5696908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5696908 prefixEnd_5696908 := by exact prefixLift 5696908
  have htrace : WordTrace (prefixWord ++ tailWord_5696908) baseStart_5696908 baseEnd_5696908 := by
    simpa [prefixWord, tailWord_5696908, baseEnd_5696908] using wordTrace_append hprefix tailTrace_5696908
  have hstable : (prefixWord ++ tailWord_5696908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5696908).length < 2 ^ (prefixWord ++ tailWord_5696908).sum := by decide
  have hdescent : baseEnd_5696908 < baseStart_5696908 := by decide
  rcases family_descends (prefixWord ++ tailWord_5696908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5696932 : List Nat := [2, 3, 1, 2, 1, 1, 1, 7, 1, 2, 2]
def baseStart_5696932 : Nat := 118140960795 + 5696932 * 2 ^ 59
def prefixEnd_5696932 : Nat := 4983230072969 + 3 ^ 40 * 5696932 * 2
def baseEnd_5696932 : Nat := 2925264371979809961050293

theorem tailTrace_5696932 : CollatzResearch.WordTrace tailWord_5696932 prefixEnd_5696932 2925264371979809961050293 := by
  unfold tailWord_5696932
  simp only [CollatzResearch.WordTrace]
  refine ⟨103892090098497898684762525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138522786797997198246350033 103892090098497898684762525)
  ·
    refine ⟨38959533786936712006785947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103892090098497898684762525 38959533786936712006785947)
    ·
      refine ⟨58439300680405068010178921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38959533786936712006785947 58439300680405068010178921)
      ·
        refine ⟨43829475510303801007634191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58439300680405068010178921 43829475510303801007634191)
        ·
          refine ⟨65744213265455701511451287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43829475510303801007634191 65744213265455701511451287)
          ·
            refine ⟨98616319898183552267176931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65744213265455701511451287 98616319898183552267176931)
            ·
              refine ⟨147924479847275328400765397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98616319898183552267176931 147924479847275328400765397)
              ·
                refine ⟨3466979996420515509392939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 147924479847275328400765397 3466979996420515509392939)
                ·
                  refine ⟨5200469994630773264089409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3466979996420515509392939 5200469994630773264089409)
                  ·
                    refine ⟨3900352495973079948067057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5200469994630773264089409 3900352495973079948067057)
                    ·
                      refine ⟨2925264371979809961050293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3900352495973079948067057 2925264371979809961050293)
                      ·
                        rfl

theorem cell23_5696932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 7, 1, 2, 2].length) (baseStart_5696932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5696932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5696932 prefixEnd_5696932 := by exact prefixLift 5696932
  have htrace : WordTrace (prefixWord ++ tailWord_5696932) baseStart_5696932 baseEnd_5696932 := by
    simpa [prefixWord, tailWord_5696932, baseEnd_5696932] using wordTrace_append hprefix tailTrace_5696932
  have hstable : (prefixWord ++ tailWord_5696932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5696932).length < 2 ^ (prefixWord ++ tailWord_5696932).sum := by decide
  have hdescent : baseEnd_5696932 < baseStart_5696932 := by decide
  rcases family_descends (prefixWord ++ tailWord_5696932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5696949 : List Nat := [1, 3, 3, 2, 2, 2, 1, 4, 1, 2, 2]
def baseStart_5696949 : Nat := 118140960795 + 5696949 * 2 ^ 59
def prefixEnd_5696949 : Nat := 4983230072969 + 3 ^ 40 * 5696949 * 2
def baseEnd_5696949 : Nat := 2925273101150936394537715

theorem tailTrace_5696949 : CollatzResearch.WordTrace tailWord_5696949 prefixEnd_5696949 2925273101150936394537715 := by
  unfold tailWord_5696949
  simp only [CollatzResearch.WordTrace]
  refine ⟨207784800237934209272893901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138523200158622806181929267 207784800237934209272893901)
  ·
    refine ⟨77919300089225328477335213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207784800237934209272893901 77919300089225328477335213)
    ·
      refine ⟨29219737533459498179000705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77919300089225328477335213 29219737533459498179000705)
      ·
        refine ⟨21914803150094623634250529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29219737533459498179000705 21914803150094623634250529)
        ·
          refine ⟨16436102362570967725687897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21914803150094623634250529 16436102362570967725687897)
          ·
            refine ⟨12327076771928225794265923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16436102362570967725687897 12327076771928225794265923)
            ·
              refine ⟨18490615157892338691398885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12327076771928225794265923 18490615157892338691398885)
              ·
                refine ⟨3466990342104813504637291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18490615157892338691398885 3466990342104813504637291)
                ·
                  refine ⟨5200485513157220256955937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3466990342104813504637291 5200485513157220256955937)
                  ·
                    refine ⟨3900364134867915192716953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5200485513157220256955937 3900364134867915192716953)
                    ·
                      refine ⟨2925273101150936394537715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3900364134867915192716953 2925273101150936394537715)
                      ·
                        rfl

theorem cell23_5696949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_5696949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5696949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5696949 prefixEnd_5696949 := by exact prefixLift 5696949
  have htrace : WordTrace (prefixWord ++ tailWord_5696949) baseStart_5696949 baseEnd_5696949 := by
    simpa [prefixWord, tailWord_5696949, baseEnd_5696949] using wordTrace_append hprefix tailTrace_5696949
  have hstable : (prefixWord ++ tailWord_5696949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5696949).length < 2 ^ (prefixWord ++ tailWord_5696949).sum := by decide
  have hdescent : baseEnd_5696949 < baseStart_5696949 := by decide
  rcases family_descends (prefixWord ++ tailWord_5696949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5696981 : List Nat := [1, 3, 2, 3, 1, 1, 1, 2, 1, 8]
def baseStart_5696981 : Nat := 118140960795 + 5696981 * 2 ^ 59
def prefixEnd_5696981 : Nat := 4983230072969 + 3 ^ 40 * 5696981 * 2
def baseEnd_5696981 : Nat := 975096510843960089779189

theorem tailTrace_5696981 : CollatzResearch.WordTrace tailWord_5696981 prefixEnd_5696981 975096510843960089779189 := by
  unfold tailWord_5696981
  simp only [CollatzResearch.WordTrace]
  refine ⟨207785967373818278738058797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138523978249212185825372531 207785967373818278738058797)
  ·
    refine ⟨77919737765181854526772049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207785967373818278738058797 77919737765181854526772049)
    ·
      refine ⟨58439803323886390895079037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77919737765181854526772049 58439803323886390895079037)
      ·
        refine ⟨21914926246457396585654639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58439803323886390895079037 21914926246457396585654639)
        ·
          refine ⟨32872389369686094878481959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21914926246457396585654639 32872389369686094878481959)
          ·
            refine ⟨49308584054529142317722939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32872389369686094878481959 49308584054529142317722939)
            ·
              refine ⟨73962876081793713476584409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49308584054529142317722939 73962876081793713476584409)
              ·
                refine ⟨55472157061345285107438307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73962876081793713476584409 55472157061345285107438307)
                ·
                  refine ⟨83208235592017927661157461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55472157061345285107438307 83208235592017927661157461)
                  ·
                    refine ⟨975096510843960089779189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 83208235592017927661157461 975096510843960089779189)
                    ·
                      rfl

theorem cell23_5696981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 8].length) (baseStart_5696981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5696981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5696981 prefixEnd_5696981 := by exact prefixLift 5696981
  have htrace : WordTrace (prefixWord ++ tailWord_5696981) baseStart_5696981 baseEnd_5696981 := by
    simpa [prefixWord, tailWord_5696981, baseEnd_5696981] using wordTrace_append hprefix tailTrace_5696981
  have hstable : (prefixWord ++ tailWord_5696981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5696981).length < 2 ^ (prefixWord ++ tailWord_5696981).sum := by decide
  have hdescent : baseEnd_5696981 < baseStart_5696981 := by decide
  rcases family_descends (prefixWord ++ tailWord_5696981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5696991 : List Nat := [1, 1, 2, 3, 3, 1, 2, 1, 1, 3, 5]
def baseStart_5696991 : Nat := 118140960795 + 5696991 * 2 ^ 59
def prefixEnd_5696991 : Nat := 4983230072969 + 3 ^ 40 * 5696991 * 2
def baseEnd_5696991 : Nat := 2925294667338425230212521

theorem tailTrace_5696991 : CollatzResearch.WordTrace tailWord_5696991 prefixEnd_5696991 2925294667338425230212521 := by
  unfold tailWord_5696991
  simp only [CollatzResearch.WordTrace]
  refine ⟨207786332103782050445922827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138524221402521366963948551 207786332103782050445922827)
  ·
    refine ⟨311679498155673075668884241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207786332103782050445922827 311679498155673075668884241)
    ·
      refine ⟨233759623616754806751663181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311679498155673075668884241 233759623616754806751663181)
      ·
        refine ⟨87659858856283052531873693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 233759623616754806751663181 87659858856283052531873693)
        ·
          refine ⟨32872447071106144699452635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87659858856283052531873693 32872447071106144699452635)
          ·
            refine ⟨49308670606659217049178953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32872447071106144699452635 49308670606659217049178953)
            ·
              refine ⟨36981502954994412786884215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49308670606659217049178953 36981502954994412786884215)
              ·
                refine ⟨55472254432491619180326323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36981502954994412786884215 55472254432491619180326323)
                ·
                  refine ⟨83208381648737428770489485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55472254432491619180326323 83208381648737428770489485)
                  ·
                    refine ⟨31203143118276535788933557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 83208381648737428770489485 31203143118276535788933557)
                    ·
                      refine ⟨2925294667338425230212521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31203143118276535788933557 2925294667338425230212521)
                      ·
                        rfl

theorem cell23_5696991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_5696991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5696991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5696991 prefixEnd_5696991 := by exact prefixLift 5696991
  have htrace : WordTrace (prefixWord ++ tailWord_5696991) baseStart_5696991 baseEnd_5696991 := by
    simpa [prefixWord, tailWord_5696991, baseEnd_5696991] using wordTrace_append hprefix tailTrace_5696991
  have hstable : (prefixWord ++ tailWord_5696991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5696991).length < 2 ^ (prefixWord ++ tailWord_5696991).sum := by decide
  have hdescent : baseEnd_5696991 < baseStart_5696991 := by decide
  rcases family_descends (prefixWord ++ tailWord_5696991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5697041 : List Nat := [1, 2, 2, 1, 1, 2, 3, 3, 1, 7]
def baseStart_5697041 : Nat := 118140960795 + 5697041 * 2 ^ 59
def prefixEnd_5697041 : Nat := 4983230072969 + 3 ^ 40 * 5697041 * 2
def baseEnd_5697041 : Nat := 975106780457050011529097

theorem tailTrace_5697041 : CollatzResearch.WordTrace tailWord_5697041 prefixEnd_5697041 975106780457050011529097 := by
  unfold tailWord_5697041
  simp only [CollatzResearch.WordTrace]
  refine ⟨207788155753600908985242977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138525437169067272656828651 207788155753600908985242977)
  ·
    refine ⟨155841116815200681738932233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207788155753600908985242977 155841116815200681738932233)
    ·
      refine ⟨116880837611400511304199175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155841116815200681738932233 116880837611400511304199175)
      ·
        refine ⟨175321256417100766956298763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116880837611400511304199175 175321256417100766956298763)
        ·
          refine ⟨262981884625651150434448145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175321256417100766956298763 262981884625651150434448145)
          ·
            refine ⟨197236413469238362825836109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 262981884625651150434448145 197236413469238362825836109)
            ·
              refine ⟨73963655050964386059688541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 197236413469238362825836109 73963655050964386059688541)
              ·
                refine ⟨27736370644111644772383203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73963655050964386059688541 27736370644111644772383203)
                ·
                  refine ⟨41604555966167467158574805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27736370644111644772383203 41604555966167467158574805)
                  ·
                    refine ⟨975106780457050011529097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41604555966167467158574805 975106780457050011529097)
                    ·
                      rfl

theorem cell23_5697041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 7].length) (baseStart_5697041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5697041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5697041 prefixEnd_5697041 := by exact prefixLift 5697041
  have htrace : WordTrace (prefixWord ++ tailWord_5697041) baseStart_5697041 baseEnd_5697041 := by
    simpa [prefixWord, tailWord_5697041, baseEnd_5697041] using wordTrace_append hprefix tailTrace_5697041
  have hstable : (prefixWord ++ tailWord_5697041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5697041).length < 2 ^ (prefixWord ++ tailWord_5697041).sum := by decide
  have hdescent : baseEnd_5697041 < baseStart_5697041 := by decide
  rcases family_descends (prefixWord ++ tailWord_5697041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5697045 : List Nat := [1, 3, 2, 1, 3, 2, 3, 3, 5]
def baseStart_5697045 : Nat := 118140960795 + 5697045 * 2 ^ 59
def prefixEnd_5697045 : Nat := 4983230072969 + 3 ^ 40 * 5697045 * 2
def baseEnd_5697045 : Nat := 325035821699307557659697

theorem tailTrace_5697045 : CollatzResearch.WordTrace tailWord_5697045 prefixEnd_5697045 325035821699307557659697 := by
  unfold tailWord_5697045
  simp only [CollatzResearch.WordTrace]
  refine ⟨207788301645586417668388589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138525534430390945112259059 207788301645586417668388589)
  ·
    refine ⟨77920613117094906625645721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207788301645586417668388589 77920613117094906625645721)
    ·
      refine ⟨58440459837821179969234291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77920613117094906625645721 58440459837821179969234291)
      ·
        refine ⟨87660689756731769953851437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58440459837821179969234291 87660689756731769953851437)
        ·
          refine ⟨32872758658774413732694289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87660689756731769953851437 32872758658774413732694289)
          ·
            refine ⟨24654568994080810299520717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32872758658774413732694289 24654568994080810299520717)
            ·
              refine ⟨9245463372780303862320269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24654568994080810299520717 9245463372780303862320269)
              ·
                refine ⟨3467048764792613948370101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9245463372780303862320269 3467048764792613948370101)
                ·
                  refine ⟨325035821699307557659697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3467048764792613948370101 325035821699307557659697)
                  ·
                    rfl

theorem cell23_5697045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 3, 5].length) (baseStart_5697045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5697045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5697045 prefixEnd_5697045 := by exact prefixLift 5697045
  have htrace : WordTrace (prefixWord ++ tailWord_5697045) baseStart_5697045 baseEnd_5697045 := by
    simpa [prefixWord, tailWord_5697045, baseEnd_5697045] using wordTrace_append hprefix tailTrace_5697045
  have hstable : (prefixWord ++ tailWord_5697045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5697045).length < 2 ^ (prefixWord ++ tailWord_5697045).sum := by decide
  have hdescent : baseEnd_5697045 < baseStart_5697045 := by decide
  rcases family_descends (prefixWord ++ tailWord_5697045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5697058 : List Nat := [3, 3, 1, 1, 1, 1, 3, 1, 4, 5]
def baseStart_5697058 : Nat := 118140960795 + 5697058 * 2 ^ 59
def prefixEnd_5697058 : Nat := 4983230072969 + 3 ^ 40 * 5697058 * 2
def baseEnd_5697058 : Nat := 975109690180758822691571

theorem tailTrace_5697058 : CollatzResearch.WordTrace tailWord_5697058 prefixEnd_5697058 975109690180758822691571 := by
  unfold tailWord_5697058
  simp only [CollatzResearch.WordTrace]
  refine ⟨51947193948634830222152957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138525850529692880592407885 51947193948634830222152957)
  ·
    refine ⟨19480197730738061333307359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51947193948634830222152957 19480197730738061333307359)
    ·
      refine ⟨29220296596107091999961039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19480197730738061333307359 29220296596107091999961039)
      ·
        refine ⟨43830444894160637999941559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29220296596107091999961039 43830444894160637999941559)
        ·
          refine ⟨65745667341240956999912339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43830444894160637999941559 65745667341240956999912339)
          ·
            refine ⟨98618501011861435499868509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65745667341240956999912339 98618501011861435499868509)
            ·
              refine ⟨36981937879448038312450691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98618501011861435499868509 36981937879448038312450691)
              ·
                refine ⟨55472906819172057468676037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36981937879448038312450691 55472906819172057468676037)
                ·
                  refine ⟨10401170028594760775376757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55472906819172057468676037 10401170028594760775376757)
                  ·
                    refine ⟨975109690180758822691571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10401170028594760775376757 975109690180758822691571)
                    ·
                      rfl

theorem cell23_5697058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_5697058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5697058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5697058 prefixEnd_5697058 := by exact prefixLift 5697058
  have htrace : WordTrace (prefixWord ++ tailWord_5697058) baseStart_5697058 baseEnd_5697058 := by
    simpa [prefixWord, tailWord_5697058, baseEnd_5697058] using wordTrace_append hprefix tailTrace_5697058
  have hstable : (prefixWord ++ tailWord_5697058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5697058).length < 2 ^ (prefixWord ++ tailWord_5697058).sum := by decide
  have hdescent : baseEnd_5697058 < baseStart_5697058 := by decide
  rcases family_descends (prefixWord ++ tailWord_5697058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5697088 : List Nat := [2, 1, 1, 2, 2, 2, 1, 3, 5, 4]
def baseStart_5697088 : Nat := 118140960795 + 5697088 * 2 ^ 59
def prefixEnd_5697088 : Nat := 4983230072969 + 3 ^ 40 * 5697088 * 2
def baseEnd_5697088 : Nat := 975114824987303783566525

theorem tailTrace_5697088 : CollatzResearch.WordTrace tailWord_5697088 prefixEnd_5697088 975114824987303783566525 := by
  unfold tailWord_5697088
  simp only [CollatzResearch.WordTrace]
  refine ⟨103894934992215318006101959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138526579989620424008135945 103894934992215318006101959)
  ·
    refine ⟨155842402488322977009152939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103894934992215318006101959 155842402488322977009152939)
    ·
      refine ⟨233763603732484465513729409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155842402488322977009152939 233763603732484465513729409)
      ·
        refine ⟨175322702799363349135297057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233763603732484465513729409 175322702799363349135297057)
        ·
          refine ⟨131492027099522511851472793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175322702799363349135297057 131492027099522511851472793)
          ·
            refine ⟨98619020324641883888604595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131492027099522511851472793 98619020324641883888604595)
            ·
              refine ⟨147928530486962825832906893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98619020324641883888604595 147928530486962825832906893)
              ·
                refine ⟨55473198932611059687340085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 147928530486962825832906893 55473198932611059687340085)
                ·
                  refine ⟨5200612399932286845688133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55473198932611059687340085 5200612399932286845688133)
                  ·
                    refine ⟨975114824987303783566525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5200612399932286845688133 975114824987303783566525)
                    ·
                      rfl

theorem cell23_5697088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 5, 4].length) (baseStart_5697088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5697088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5697088 prefixEnd_5697088 := by exact prefixLift 5697088
  have htrace : WordTrace (prefixWord ++ tailWord_5697088) baseStart_5697088 baseEnd_5697088 := by
    simpa [prefixWord, tailWord_5697088, baseEnd_5697088] using wordTrace_append hprefix tailTrace_5697088
  have hstable : (prefixWord ++ tailWord_5697088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5697088).length < 2 ^ (prefixWord ++ tailWord_5697088).sum := by decide
  have hdescent : baseEnd_5697088 < baseStart_5697088 := by decide
  rcases family_descends (prefixWord ++ tailWord_5697088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5697091 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 6]
def baseStart_5697091 : Nat := 118140960795 + 5697091 * 2 ^ 59
def prefixEnd_5697091 : Nat := 4983230072969 + 3 ^ 40 * 5697091 * 2
def baseEnd_5697091 : Nat := 2925346015403874838962061

theorem tailTrace_5697091 : CollatzResearch.WordTrace tailWord_5697091 prefixEnd_5697091 2925346015403874838962061 := by
  unfold tailWord_5697091
  simp only [CollatzResearch.WordTrace]
  refine ⟨207789979403419767524563127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138526652935613178349708751 207789979403419767524563127)
  ·
    refine ⟨311684969105129651286844691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207789979403419767524563127 311684969105129651286844691)
    ·
      refine ⟨467527453657694476930267037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311684969105129651286844691 467527453657694476930267037)
      ·
        refine ⟨175322795121635428848850139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 467527453657694476930267037 175322795121635428848850139)
        ·
          refine ⟨262984192682453143273275209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175322795121635428848850139 262984192682453143273275209)
          ·
            refine ⟨197238144511839857454956407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 262984192682453143273275209 197238144511839857454956407)
            ·
              refine ⟨295857216767759786182434611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197238144511839857454956407 295857216767759786182434611)
              ·
                refine ⟨443785825151639679273651917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 295857216767759786182434611 443785825151639679273651917)
                ·
                  refine ⟨166419684431864879727619469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 443785825151639679273651917 166419684431864879727619469)
                  ·
                    refine ⟨62407381661949329897857301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 166419684431864879727619469 62407381661949329897857301)
                    ·
                      refine ⟨2925346015403874838962061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62407381661949329897857301 2925346015403874838962061)
                      ·
                        rfl

theorem cell23_5697091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 6].length) (baseStart_5697091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5697091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5697091 prefixEnd_5697091 := by exact prefixLift 5697091
  have htrace : WordTrace (prefixWord ++ tailWord_5697091) baseStart_5697091 baseEnd_5697091 := by
    simpa [prefixWord, tailWord_5697091, baseEnd_5697091] using wordTrace_append hprefix tailTrace_5697091
  have hstable : (prefixWord ++ tailWord_5697091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5697091).length < 2 ^ (prefixWord ++ tailWord_5697091).sum := by decide
  have hdescent : baseEnd_5697091 < baseStart_5697091 := by decide
  rcases family_descends (prefixWord ++ tailWord_5697091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5697108 : List Nat := [2, 4, 1, 1, 1, 2, 2, 1, 2, 1, 6]
def baseStart_5697108 : Nat := 118140960795 + 5697108 * 2 ^ 59
def prefixEnd_5697108 : Nat := 4983230072969 + 3 ^ 40 * 5697108 * 2
def baseEnd_5697108 : Nat := 2925354744575001272449483

theorem tailTrace_5697108 : CollatzResearch.WordTrace tailWord_5697108 prefixEnd_5697108 2925354744575001272449483 := by
  unfold tailWord_5697108
  simp only [CollatzResearch.WordTrace]
  refine ⟨103895299722179089713965989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138527066296238786285287985 103895299722179089713965989)
  ·
    refine ⟨19480368697908579321368623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103895299722179089713965989 19480368697908579321368623)
    ·
      refine ⟨29220553046862868982052935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19480368697908579321368623 29220553046862868982052935)
      ·
        refine ⟨43830829570294303473079403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29220553046862868982052935 43830829570294303473079403)
        ·
          refine ⟨65746244355441455209619105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43830829570294303473079403 65746244355441455209619105)
          ·
            refine ⟨49309683266581091407214329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65746244355441455209619105 49309683266581091407214329)
            ·
              refine ⟨36982262449935818555410747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49309683266581091407214329 36982262449935818555410747)
              ·
                refine ⟨55473393674903727833116121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36982262449935818555410747 55473393674903727833116121)
                ·
                  refine ⟨41605045256177795874837091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55473393674903727833116121 41605045256177795874837091)
                  ·
                    refine ⟨62407567884266693812255637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41605045256177795874837091 62407567884266693812255637)
                    ·
                      refine ⟨2925354744575001272449483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62407567884266693812255637 2925354744575001272449483)
                      ·
                        rfl

theorem cell23_5697108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_5697108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5697108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5697108 prefixEnd_5697108 := by exact prefixLift 5697108
  have htrace : WordTrace (prefixWord ++ tailWord_5697108) baseStart_5697108 baseEnd_5697108 := by
    simpa [prefixWord, tailWord_5697108, baseEnd_5697108] using wordTrace_append hprefix tailTrace_5697108
  have hstable : (prefixWord ++ tailWord_5697108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5697108).length < 2 ^ (prefixWord ++ tailWord_5697108).sum := by decide
  have hdescent : baseEnd_5697108 < baseStart_5697108 := by decide
  rcases family_descends (prefixWord ++ tailWord_5697108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5697229 : List Nat := [1, 6, 2, 1, 1, 1, 2, 1, 4, 4]
def baseStart_5697229 : Nat := 118140960795 + 5697229 * 2 ^ 59
def prefixEnd_5697229 : Nat := 4983230072969 + 3 ^ 40 * 5697229 * 2
def baseEnd_5697229 : Nat := 975138958578065099678809

theorem tailTrace_5697229 : CollatzResearch.WordTrace tailWord_5697229 prefixEnd_5697229 975138958578065099678809 := by
  unfold tailWord_5697229
  simp only [CollatzResearch.WordTrace]
  refine ⟨207795012676919817093086741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138530008451279878062057827 207795012676919817093086741)
  ·
    refine ⟨9740391219230616426238441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 207795012676919817093086741 9740391219230616426238441)
    ·
      refine ⟨7305293414422962319678831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9740391219230616426238441 7305293414422962319678831)
      ·
        refine ⟨10957940121634443479518247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7305293414422962319678831 10957940121634443479518247)
        ·
          refine ⟨16436910182451665219277371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10957940121634443479518247 16436910182451665219277371)
          ·
            refine ⟨24655365273677497828916057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16436910182451665219277371 24655365273677497828916057)
            ·
              refine ⟨18491523955258123371687043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24655365273677497828916057 18491523955258123371687043)
              ·
                refine ⟨27737285932887185057530565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18491523955258123371687043 27737285932887185057530565)
                ·
                  refine ⟨5200741112416347198286981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27737285932887185057530565 5200741112416347198286981)
                  ·
                    refine ⟨975138958578065099678809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5200741112416347198286981 975138958578065099678809)
                    ·
                      rfl

theorem cell23_5697229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_5697229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5697229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5697229 prefixEnd_5697229 := by exact prefixLift 5697229
  have htrace : WordTrace (prefixWord ++ tailWord_5697229) baseStart_5697229 baseEnd_5697229 := by
    simpa [prefixWord, tailWord_5697229, baseEnd_5697229] using wordTrace_append hprefix tailTrace_5697229
  have hstable : (prefixWord ++ tailWord_5697229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5697229).length < 2 ^ (prefixWord ++ tailWord_5697229).sum := by decide
  have hdescent : baseEnd_5697229 < baseStart_5697229 := by decide
  rcases family_descends (prefixWord ++ tailWord_5697229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5697236 : List Nat := [2, 4, 1, 3, 1, 1, 3, 1, 3, 2, 2]
def baseStart_5697236 : Nat := 118140960795 + 5697236 * 2 ^ 59
def prefixEnd_5697236 : Nat := 4983230072969 + 3 ^ 40 * 5697236 * 2
def baseEnd_5697236 : Nat := 2925420470098776771648895

theorem tailTrace_5697236 : CollatzResearch.WordTrace tailWord_5697236 prefixEnd_5697236 2925420470098776771648895 := by
  unfold tailWord_5697236
  simp only [CollatzResearch.WordTrace]
  refine ⟨103897633993947228644295781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138530178658596304859061041 103897633993947228644295781)
  ·
    refine ⟨19480806373865105370805459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103897633993947228644295781 19480806373865105370805459)
    ·
      refine ⟨29221209560797658056208189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19480806373865105370805459 29221209560797658056208189)
      ·
        refine ⟨10957953585299121771078071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29221209560797658056208189 10957953585299121771078071)
        ·
          refine ⟨16436930377948682656617107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10957953585299121771078071 16436930377948682656617107)
          ·
            refine ⟨24655395566923023984925661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16436930377948682656617107 24655395566923023984925661)
            ·
              refine ⟨9245773337596133994347123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24655395566923023984925661 9245773337596133994347123)
              ·
                refine ⟨13868660006394200991520685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9245773337596133994347123 13868660006394200991520685)
                ·
                  refine ⟨5200747502397825371820257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13868660006394200991520685 5200747502397825371820257)
                  ·
                    refine ⟨3900560626798369028865193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5200747502397825371820257 3900560626798369028865193)
                    ·
                      refine ⟨2925420470098776771648895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3900560626798369028865193 2925420470098776771648895)
                      ·
                        rfl

theorem cell23_5697236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_5697236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5697236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5697236 prefixEnd_5697236 := by exact prefixLift 5697236
  have htrace : WordTrace (prefixWord ++ tailWord_5697236) baseStart_5697236 baseEnd_5697236 := by
    simpa [prefixWord, tailWord_5697236, baseEnd_5697236] using wordTrace_append hprefix tailTrace_5697236
  have hstable : (prefixWord ++ tailWord_5697236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5697236).length < 2 ^ (prefixWord ++ tailWord_5697236).sum := by decide
  have hdescent : baseEnd_5697236 < baseStart_5697236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5697236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5697287 : List Nat := [1, 1, 4, 4, 3, 1, 2, 2, 1, 2, 2]
def baseStart_5697287 : Nat := 118140960795 + 5697287 * 2 ^ 59
def prefixEnd_5697287 : Nat := 4983230072969 + 3 ^ 40 * 5697287 * 2
def baseEnd_5697287 : Nat := 2925446657612156072111161

theorem tailTrace_5697287 : CollatzResearch.WordTrace tailWord_5697287 prefixEnd_5697287 2925446657612156072111161 := by
  unfold tailWord_5697287
  simp only [CollatzResearch.WordTrace]
  refine ⟨207797128110709692998698115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138531418740473128665798743 207797128110709692998698115)
  ·
    refine ⟨311695692166064539498047173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207797128110709692998698115 311695692166064539498047173)
    ·
      refine ⟨58442942281137101155883845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 311695692166064539498047173 58442942281137101155883845)
      ·
        refine ⟨10958051677713206466728221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58442942281137101155883845 10958051677713206466728221)
        ·
          refine ⟨4109269379142452425023083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10958051677713206466728221 4109269379142452425023083)
          ·
            refine ⟨6163904068713678637534625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4109269379142452425023083 6163904068713678637534625)
            ·
              refine ⟨4622928051535258978150969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6163904068713678637534625 4622928051535258978150969)
              ·
                refine ⟨3467196038651444233613227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4622928051535258978150969 3467196038651444233613227)
                ·
                  refine ⟨5200794057977166350419841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3467196038651444233613227 5200794057977166350419841)
                  ·
                    refine ⟨3900595543482874762814881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5200794057977166350419841 3900595543482874762814881)
                    ·
                      refine ⟨2925446657612156072111161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3900595543482874762814881 2925446657612156072111161)
                      ·
                        rfl

theorem cell23_5697287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_5697287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5697287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5697287 prefixEnd_5697287 := by exact prefixLift 5697287
  have htrace : WordTrace (prefixWord ++ tailWord_5697287) baseStart_5697287 baseEnd_5697287 := by
    simpa [prefixWord, tailWord_5697287, baseEnd_5697287] using wordTrace_append hprefix tailTrace_5697287
  have hstable : (prefixWord ++ tailWord_5697287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5697287).length < 2 ^ (prefixWord ++ tailWord_5697287).sum := by decide
  have hdescent : baseEnd_5697287 < baseStart_5697287 := by decide
  rcases family_descends (prefixWord ++ tailWord_5697287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5697293 : List Nat := [1, 7, 2, 1, 1, 2, 1, 8]
def baseStart_5697293 : Nat := 118140960795 + 5697293 * 2 ^ 59
def prefixEnd_5697293 : Nat := 4983230072969 + 3 ^ 40 * 5697293 * 2
def baseEnd_5697293 : Nat := 108349990314669742542079

theorem tailTrace_5697293 : CollatzResearch.WordTrace tailWord_5697293 prefixEnd_5697293 108349990314669742542079 := by
  unfold tailWord_5697293
  simp only [CollatzResearch.WordTrace]
  refine ⟨207797346948687956023416533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138531564632458637348944355 207797346948687956023416533)
  ·
    refine ⟨4870250319109873969298825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 207797346948687956023416533 4870250319109873969298825)
    ·
      refine ⟨3652687739332405476974119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4870250319109873969298825 3652687739332405476974119)
      ·
        refine ⟨5479031608998608215461179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3652687739332405476974119 5479031608998608215461179)
        ·
          refine ⟨8218547413497912323191769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5479031608998608215461179 8218547413497912323191769)
          ·
            refine ⟨6163910560123434242393827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8218547413497912323191769 6163910560123434242393827)
            ·
              refine ⟨9245865840185151363590741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6163910560123434242393827 9245865840185151363590741)
              ·
                refine ⟨108349990314669742542079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9245865840185151363590741 108349990314669742542079)
                ·
                  rfl

theorem cell23_5697293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 8].length) (baseStart_5697293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5697293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5697293 prefixEnd_5697293 := by exact prefixLift 5697293
  have htrace : WordTrace (prefixWord ++ tailWord_5697293) baseStart_5697293 baseEnd_5697293 := by
    simpa [prefixWord, tailWord_5697293, baseEnd_5697293] using wordTrace_append hprefix tailTrace_5697293
  have hstable : (prefixWord ++ tailWord_5697293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5697293).length < 2 ^ (prefixWord ++ tailWord_5697293).sum := by decide
  have hdescent : baseEnd_5697293 < baseStart_5697293 := by decide
  rcases family_descends (prefixWord ++ tailWord_5697293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5697343 : List Nat := [1, 1, 2, 2, 6, 2, 1, 2, 2, 2, 2]
def baseStart_5697343 : Nat := 118140960795 + 5697343 * 2 ^ 59
def prefixEnd_5697343 : Nat := 4983230072969 + 3 ^ 40 * 5697343 * 2
def baseEnd_5697343 : Nat := 2925475412528807853010903

theorem tailTrace_5697343 : CollatzResearch.WordTrace tailWord_5697343 prefixEnd_5697343 2925475412528807853010903 := by
  unfold tailWord_5697343
  simp only [CollatzResearch.WordTrace]
  refine ⟨207799170598506814562736683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138532780399004543041824455 207799170598506814562736683)
  ·
    refine ⟨311698755897760221844105025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207799170598506814562736683 311698755897760221844105025)
    ·
      refine ⟨233774066923320166383078769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311698755897760221844105025 233774066923320166383078769)
      ·
        refine ⟨175330550192490124787309077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233774066923320166383078769 175330550192490124787309077)
        ·
          refine ⟨8218619540272974599405113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 175330550192490124787309077 8218619540272974599405113)
          ·
            refine ⟨6163964655204730949553835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8218619540272974599405113 6163964655204730949553835)
            ·
              refine ⟨9245946982807096424330753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6163964655204730949553835 9245946982807096424330753)
              ·
                refine ⟨6934460237105322318248065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9245946982807096424330753 6934460237105322318248065)
                ·
                  refine ⟨5200845177828991738686049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6934460237105322318248065 5200845177828991738686049)
                  ·
                    refine ⟨3900633883371743804014537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5200845177828991738686049 3900633883371743804014537)
                    ·
                      refine ⟨2925475412528807853010903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3900633883371743804014537 2925475412528807853010903)
                      ·
                        rfl

theorem cell23_5697343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 2, 2, 2, 2].length) (baseStart_5697343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5697343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5697343 prefixEnd_5697343 := by exact prefixLift 5697343
  have htrace : WordTrace (prefixWord ++ tailWord_5697343) baseStart_5697343 baseEnd_5697343 := by
    simpa [prefixWord, tailWord_5697343, baseEnd_5697343] using wordTrace_append hprefix tailTrace_5697343
  have hstable : (prefixWord ++ tailWord_5697343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5697343).length < 2 ^ (prefixWord ++ tailWord_5697343).sum := by decide
  have hdescent : baseEnd_5697343 < baseStart_5697343 := by decide
  rcases family_descends (prefixWord ++ tailWord_5697343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5697402 : List Nat := [3, 1, 1, 1, 1, 1, 5, 1, 4, 2, 3]
def baseStart_5697402 : Nat := 118140960795 + 5697402 * 2 ^ 59
def prefixEnd_5697402 : Nat := 4983230072969 + 3 ^ 40 * 5697402 * 2
def baseEnd_5697402 : Nat := 2925505707887423122173131

theorem tailTrace_5697402 : CollatzResearch.WordTrace tailWord_5697402 prefixEnd_5697402 2925505707887423122173131 := by
  unfold tailWord_5697402
  simp only [CollatzResearch.WordTrace]
  refine ⟨51950330626323266909783615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138534215003528711759422973 51950330626323266909783615)
  ·
    refine ⟨77925495939484900364675423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51950330626323266909783615 77925495939484900364675423)
    ·
      refine ⟨116888243909227350547013135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77925495939484900364675423 116888243909227350547013135)
      ·
        refine ⟨175332365863841025820519703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116888243909227350547013135 175332365863841025820519703)
        ·
          refine ⟨262998548795761538730779555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175332365863841025820519703 262998548795761538730779555)
          ·
            refine ⟨394497823193642308096169333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262998548795761538730779555 394497823193642308096169333)
            ·
              refine ⟨36984170924403966384015875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 394497823193642308096169333 36984170924403966384015875)
              ·
                refine ⟨55476256386605949576023813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36984170924403966384015875 55476256386605949576023813)
                ·
                  refine ⟨10401798072488615545504465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55476256386605949576023813 10401798072488615545504465)
                  ·
                    refine ⟨7801348554366461659128349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10401798072488615545504465 7801348554366461659128349)
                    ·
                      refine ⟨2925505707887423122173131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7801348554366461659128349 2925505707887423122173131)
                      ·
                        rfl

theorem cell23_5697402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 4, 2, 3].length) (baseStart_5697402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5697402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5697402 prefixEnd_5697402 := by exact prefixLift 5697402
  have htrace : WordTrace (prefixWord ++ tailWord_5697402) baseStart_5697402 baseEnd_5697402 := by
    simpa [prefixWord, tailWord_5697402, baseEnd_5697402] using wordTrace_append hprefix tailTrace_5697402
  have hstable : (prefixWord ++ tailWord_5697402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5697402).length < 2 ^ (prefixWord ++ tailWord_5697402).sum := by decide
  have hdescent : baseEnd_5697402 < baseStart_5697402 := by decide
  rcases family_descends (prefixWord ++ tailWord_5697402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5697425 : List Nat := [1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 6]
def baseStart_5697425 : Nat := 118140960795 + 5697425 * 2 ^ 59
def prefixEnd_5697425 : Nat := 4983230072969 + 3 ^ 40 * 5697425 * 2
def baseEnd_5697425 : Nat := 2925517517942476532185525

theorem tailTrace_5697425 : CollatzResearch.WordTrace tailWord_5697425 prefixEnd_5697425 2925517517942476532185525 := by
  unfold tailWord_5697425
  simp only [CollatzResearch.WordTrace]
  refine ⟨207802161384209742567221729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138534774256139828378147819 207802161384209742567221729)
  ·
    refine ⟨155851621038157306925416297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207802161384209742567221729 155851621038157306925416297)
    ·
      refine ⟨116888715778617980194062223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155851621038157306925416297 116888715778617980194062223)
      ·
        refine ⟨175333073667926970291093335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116888715778617980194062223 175333073667926970291093335)
        ·
          refine ⟨262999610501890455436640003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175333073667926970291093335 262999610501890455436640003)
          ·
            refine ⟨394499415752835683154960005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262999610501890455436640003 394499415752835683154960005)
            ·
              refine ⟨73968640453656690591555001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 394499415752835683154960005 73968640453656690591555001)
              ·
                refine ⟨55476480340242517943666251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73968640453656690591555001 55476480340242517943666251)
                ·
                  refine ⟨83214720510363776915499377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55476480340242517943666251 83214720510363776915499377)
                  ·
                    refine ⟨62411040382772832686624533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 83214720510363776915499377 62411040382772832686624533)
                    ·
                      refine ⟨2925517517942476532185525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62411040382772832686624533 2925517517942476532185525)
                      ·
                        rfl

theorem cell23_5697425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 6].length) (baseStart_5697425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5697425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5697425 prefixEnd_5697425 := by exact prefixLift 5697425
  have htrace : WordTrace (prefixWord ++ tailWord_5697425) baseStart_5697425 baseEnd_5697425 := by
    simpa [prefixWord, tailWord_5697425, baseEnd_5697425] using wordTrace_append hprefix tailTrace_5697425
  have hstable : (prefixWord ++ tailWord_5697425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5697425).length < 2 ^ (prefixWord ++ tailWord_5697425).sum := by decide
  have hdescent : baseEnd_5697425 < baseStart_5697425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5697425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5697436 : List Nat := [2, 2, 3, 3, 1, 2, 2, 1, 2, 2, 3]
def baseStart_5697436 : Nat := 118140960795 + 5697436 * 2 ^ 59
def prefixEnd_5697436 : Nat := 4983230072969 + 3 ^ 40 * 5697436 * 2
def baseEnd_5697436 : Nat := 2925523166229675989147975

theorem tailTrace_5697436 : CollatzResearch.WordTrace tailWord_5697436 prefixEnd_5697436 2925523166229675989147975 := by
  unfold tailWord_5697436
  simp only [CollatzResearch.WordTrace]
  refine ⟨103901281293584945722936081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138535041724779927630581441 103901281293584945722936081)
  ·
    refine ⟨77925960970188709292202061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103901281293584945722936081 77925960970188709292202061)
    ·
      refine ⟨29222235363820765984575773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77925960970188709292202061 29222235363820765984575773)
      ·
        refine ⟨10958338261432787244215915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29222235363820765984575773 10958338261432787244215915)
        ·
          refine ⟨16437507392149180866323873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10958338261432787244215915 16437507392149180866323873)
          ·
            refine ⟨12328130544111885649742905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16437507392149180866323873 12328130544111885649742905)
            ·
              refine ⟨9246097908083914237307179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12328130544111885649742905 9246097908083914237307179)
              ·
                refine ⟨13869146862125871355960769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9246097908083914237307179 13869146862125871355960769)
                ·
                  refine ⟨10401860146594403516970577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13869146862125871355960769 10401860146594403516970577)
                  ·
                    refine ⟨7801395109945802637727933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10401860146594403516970577 7801395109945802637727933)
                    ·
                      refine ⟨2925523166229675989147975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7801395109945802637727933 2925523166229675989147975)
                      ·
                        rfl

theorem cell23_5697436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_5697436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5697436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5697436 prefixEnd_5697436 := by exact prefixLift 5697436
  have htrace : WordTrace (prefixWord ++ tailWord_5697436) baseStart_5697436 baseEnd_5697436 := by
    simpa [prefixWord, tailWord_5697436, baseEnd_5697436] using wordTrace_append hprefix tailTrace_5697436
  have hstable : (prefixWord ++ tailWord_5697436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5697436).length < 2 ^ (prefixWord ++ tailWord_5697436).sum := by decide
  have hdescent : baseEnd_5697436 < baseStart_5697436 := by decide
  rcases family_descends (prefixWord ++ tailWord_5697436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5697445 : List Nat := [1, 3, 1, 2, 1, 1, 1, 2, 1, 3, 7]
def baseStart_5697445 : Nat := 118140960795 + 5697445 * 2 ^ 59
def prefixEnd_5697445 : Nat := 4983230072969 + 3 ^ 40 * 5697445 * 2
def baseEnd_5697445 : Nat := 2925527787555566453935433

theorem tailTrace_5697445 : CollatzResearch.WordTrace tailWord_5697445 prefixEnd_5697445 2925527787555566453935433 := by
  unfold tailWord_5697445
  simp only [CollatzResearch.WordTrace]
  refine ⟨207802890844137285982949789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138535260562758190655299859 207802890844137285982949789)
  ·
    refine ⟨77926084066551482243606171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207802890844137285982949789 77926084066551482243606171)
    ·
      refine ⟨116889126099827223365409257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77926084066551482243606171 116889126099827223365409257)
      ·
        refine ⟨87666844574870417524056943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116889126099827223365409257 87666844574870417524056943)
        ·
          refine ⟨131500266862305626286085415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87666844574870417524056943 131500266862305626286085415)
          ·
            refine ⟨197250400293458439429128123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131500266862305626286085415 197250400293458439429128123)
            ·
              refine ⟨295875600440187659143692185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197250400293458439429128123 295875600440187659143692185)
              ·
                refine ⟨221906700330140744357769139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 295875600440187659143692185 221906700330140744357769139)
                ·
                  refine ⟨332860050495211116536653709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 221906700330140744357769139 332860050495211116536653709)
                  ·
                    refine ⟨124822518935704168701245141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 332860050495211116536653709 124822518935704168701245141)
                    ·
                      refine ⟨2925527787555566453935433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 124822518935704168701245141 2925527787555566453935433)
                      ·
                        rfl

theorem cell23_5697445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_5697445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5697445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5697445 prefixEnd_5697445 := by exact prefixLift 5697445
  have htrace : WordTrace (prefixWord ++ tailWord_5697445) baseStart_5697445 baseEnd_5697445 := by
    simpa [prefixWord, tailWord_5697445, baseEnd_5697445] using wordTrace_append hprefix tailTrace_5697445
  have hstable : (prefixWord ++ tailWord_5697445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5697445).length < 2 ^ (prefixWord ++ tailWord_5697445).sum := by decide
  have hdescent : baseEnd_5697445 < baseStart_5697445 := by decide
  rcases family_descends (prefixWord ++ tailWord_5697445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5697459 : List Nat := [1, 1, 1, 2, 3, 1, 3, 4, 2, 3, 2]
def baseStart_5697459 : Nat := 118140960795 + 5697459 * 2 ^ 59
def prefixEnd_5697459 : Nat := 4983230072969 + 3 ^ 40 * 5697459 * 2
def baseEnd_5697459 : Nat := 2925534976284729399160369

theorem tailTrace_5697459 : CollatzResearch.WordTrace tailWord_5697459 prefixEnd_5697459 2925534976284729399160369 := by
  unfold tailWord_5697459
  simp only [CollatzResearch.WordTrace]
  refine ⟨207803401466086566373959431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138535600977391044249306287 207803401466086566373959431)
  ·
    refine ⟨311705102199129849560939147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207803401466086566373959431 311705102199129849560939147)
    ·
      refine ⟨467557653298694774341408721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311705102199129849560939147 467557653298694774341408721)
      ·
        refine ⟨350668239974021080756056541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 467557653298694774341408721 350668239974021080756056541)
        ·
          refine ⟨131500589990257905283521203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 350668239974021080756056541 131500589990257905283521203)
          ·
            refine ⟨197250884985386857925281805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131500589990257905283521203 197250884985386857925281805)
            ·
              refine ⟨73969081869520071721980677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 197250884985386857925281805 73969081869520071721980677)
              ·
                refine ⟨13869202850535013447871377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73969081869520071721980677 13869202850535013447871377)
                ·
                  refine ⟨10401902137901260085903533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13869202850535013447871377 10401902137901260085903533)
                  ·
                    refine ⟨3900713301712972532213825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10401902137901260085903533 3900713301712972532213825)
                    ·
                      refine ⟨2925534976284729399160369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3900713301712972532213825 2925534976284729399160369)
                      ·
                        rfl

theorem cell23_5697459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4, 2, 3, 2].length) (baseStart_5697459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5697459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5697459 prefixEnd_5697459 := by exact prefixLift 5697459
  have htrace : WordTrace (prefixWord ++ tailWord_5697459) baseStart_5697459 baseEnd_5697459 := by
    simpa [prefixWord, tailWord_5697459, baseEnd_5697459] using wordTrace_append hprefix tailTrace_5697459
  have hstable : (prefixWord ++ tailWord_5697459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5697459).length < 2 ^ (prefixWord ++ tailWord_5697459).sum := by decide
  have hdescent : baseEnd_5697459 < baseStart_5697459 := by decide
  rcases family_descends (prefixWord ++ tailWord_5697459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5697460 : List Nat := [2, 5, 2, 1, 2, 1, 1, 4, 1, 4]
def baseStart_5697460 : Nat := 118140960795 + 5697460 * 2 ^ 59
def prefixEnd_5697460 : Nat := 4983230072969 + 3 ^ 40 * 5697460 * 2
def baseEnd_5697460 : Nat := 975178496588461298415955

theorem tailTrace_5697460 : CollatzResearch.WordTrace tailWord_5697460 prefixEnd_5697460 975178496588461298415955 := by
  unfold tailWord_5697460
  simp only [CollatzResearch.WordTrace]
  refine ⟨103901718969541471772372917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138535625292721962363163889 103901718969541471772372917)
  ·
    refine ⟨9740786153394512978659961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 103901718969541471772372917 9740786153394512978659961)
    ·
      refine ⟨7305589615045884733994971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9740786153394512978659961 7305589615045884733994971)
      ·
        refine ⟨10958384422568827100992457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7305589615045884733994971 10958384422568827100992457)
        ·
          refine ⟨8218788316926620325744343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10958384422568827100992457 8218788316926620325744343)
          ·
            refine ⟨12328182475389930488616515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8218788316926620325744343 12328182475389930488616515)
            ·
              refine ⟨18492273713084895732924773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12328182475389930488616515 18492273713084895732924773)
              ·
                refine ⟨3467301321203417949923395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18492273713084895732924773 3467301321203417949923395)
                ·
                  refine ⟨5200951981805126924885093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3467301321203417949923395 5200951981805126924885093)
                  ·
                    refine ⟨975178496588461298415955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5200951981805126924885093 975178496588461298415955)
                    ·
                      rfl

theorem cell23_5697460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_5697460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5697460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5697460 prefixEnd_5697460 := by exact prefixLift 5697460
  have htrace : WordTrace (prefixWord ++ tailWord_5697460) baseStart_5697460 baseEnd_5697460 := by
    simpa [prefixWord, tailWord_5697460, baseEnd_5697460] using wordTrace_append hprefix tailTrace_5697460
  have hstable : (prefixWord ++ tailWord_5697460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5697460).length < 2 ^ (prefixWord ++ tailWord_5697460).sum := by decide
  have hdescent : baseEnd_5697460 < baseStart_5697460 := by decide
  rcases family_descends (prefixWord ++ tailWord_5697460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5697472 : List Nat := [2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 4]
def baseStart_5697472 : Nat := 118140960795 + 5697472 * 2 ^ 59
def prefixEnd_5697472 : Nat := 4983230072969 + 3 ^ 40 * 5697472 * 2
def baseEnd_5697472 : Nat := 2925541651533237848297809

theorem tailTrace_5697472 : CollatzResearch.WordTrace tailWord_5697472 prefixEnd_5697472 2925541651533237848297809 := by
  unfold tailWord_5697472
  simp only [CollatzResearch.WordTrace]
  refine ⟨103901937807519734797091335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138535917076692979729455113 103901937807519734797091335)
  ·
    refine ⟨155852906711279602195637003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103901937807519734797091335 155852906711279602195637003)
    ·
      refine ⟨233779360066919403293455505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155852906711279602195637003 233779360066919403293455505)
      ·
        refine ⟨175334520050189552470091629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233779360066919403293455505 175334520050189552470091629)
        ·
          refine ⟨65750445018821082176284361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175334520050189552470091629 65750445018821082176284361)
          ·
            refine ⟨49312833764115811632213271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65750445018821082176284361 49312833764115811632213271)
            ·
              refine ⟨73969250646173717448319907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49312833764115811632213271 73969250646173717448319907)
              ·
                refine ⟨110953875969260576172479861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73969250646173717448319907 110953875969260576172479861)
                ·
                  refine ⟨10401925872118179016169987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 110953875969260576172479861 10401925872118179016169987)
                  ·
                    refine ⟨15602888808177268524254981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10401925872118179016169987 15602888808177268524254981)
                    ·
                      refine ⟨2925541651533237848297809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15602888808177268524254981 2925541651533237848297809)
                      ·
                        rfl

theorem cell23_5697472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 4].length) (baseStart_5697472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5697472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5697472 prefixEnd_5697472 := by exact prefixLift 5697472
  have htrace : WordTrace (prefixWord ++ tailWord_5697472) baseStart_5697472 baseEnd_5697472 := by
    simpa [prefixWord, tailWord_5697472, baseEnd_5697472] using wordTrace_append hprefix tailTrace_5697472
  have hstable : (prefixWord ++ tailWord_5697472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5697472).length < 2 ^ (prefixWord ++ tailWord_5697472).sum := by decide
  have hdescent : baseEnd_5697472 < baseStart_5697472 := by decide
  rcases family_descends (prefixWord ++ tailWord_5697472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5697482 : List Nat := [3, 1, 2, 1, 2, 1, 3, 3, 1, 6]
def baseStart_5697482 : Nat := 118140960795 + 5697482 * 2 ^ 59
def prefixEnd_5697482 : Nat := 4983230072969 + 3 ^ 40 * 5697482 * 2
def baseEnd_5697482 : Nat := 975182262113260936390921

theorem tailTrace_5697482 : CollatzResearch.WordTrace tailWord_5697482 prefixEnd_5697482 975182262113260936390921 := by
  unfold tailWord_5697482
  simp only [CollatzResearch.WordTrace]
  refine ⟨51951060086250810325511675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138536160230002160868031133 51951060086250810325511675)
  ·
    refine ⟨77926590129376215488267513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51951060086250810325511675 77926590129376215488267513)
    ·
      refine ⟨58444942597032161616200635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77926590129376215488267513 58444942597032161616200635)
      ·
        refine ⟨87667413895548242424300953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58444942597032161616200635 87667413895548242424300953)
        ·
          refine ⟨65750560421661181818225715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87667413895548242424300953 65750560421661181818225715)
          ·
            refine ⟨98625840632491772727338573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65750560421661181818225715 98625840632491772727338573)
            ·
              refine ⟨36984690237184414772751965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98625840632491772727338573 36984690237184414772751965)
              ·
                refine ⟨13869258838944155539781987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36984690237184414772751965 13869258838944155539781987)
                ·
                  refine ⟨20803888258416233309672981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13869258838944155539781987 20803888258416233309672981)
                  ·
                    refine ⟨975182262113260936390921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20803888258416233309672981 975182262113260936390921)
                    ·
                      rfl

theorem cell23_5697482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3, 1, 6].length) (baseStart_5697482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5697482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5697482 prefixEnd_5697482 := by exact prefixLift 5697482
  have htrace : WordTrace (prefixWord ++ tailWord_5697482) baseStart_5697482 baseEnd_5697482 := by
    simpa [prefixWord, tailWord_5697482, baseEnd_5697482] using wordTrace_append hprefix tailTrace_5697482
  have hstable : (prefixWord ++ tailWord_5697482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5697482).length < 2 ^ (prefixWord ++ tailWord_5697482).sum := by decide
  have hdescent : baseEnd_5697482 < baseStart_5697482 := by decide
  rcases family_descends (prefixWord ++ tailWord_5697482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5697493 : List Nat := [1, 3, 2, 3, 2, 3, 1, 1, 2, 3, 2]
def baseStart_5697493 : Nat := 118140960795 + 5697493 * 2 ^ 59
def prefixEnd_5697493 : Nat := 4983230072969 + 3 ^ 40 * 5697493 * 2
def baseEnd_5697493 : Nat := 2925552434626982266135213

theorem tailTrace_5697493 : CollatzResearch.WordTrace tailWord_5697493 prefixEnd_5697493 2925552434626982266135213 := by
  unfold tailWord_5697493
  simp only [CollatzResearch.WordTrace]
  refine ⟨207804641547963390180697133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138536427698642260120464755 207804641547963390180697133)
  ·
    refine ⟨77926740580486271317761425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207804641547963390180697133 77926740580486271317761425)
    ·
      refine ⟨58445055435364703488321069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77926740580486271317761425 58445055435364703488321069)
      ·
        refine ⟨21916895788261763808120401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58445055435364703488321069 21916895788261763808120401)
        ·
          refine ⟨16437671841196322856090301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21916895788261763808120401 16437671841196322856090301)
          ·
            refine ⟨6164126940448621071033863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16437671841196322856090301 6164126940448621071033863)
            ·
              refine ⟨9246190410672931606550795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6164126940448621071033863 9246190410672931606550795)
              ·
                refine ⟨13869285616009397409826193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9246190410672931606550795 13869285616009397409826193)
                ·
                  refine ⟨10401964212007048057369645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13869285616009397409826193 10401964212007048057369645)
                  ·
                    refine ⟨3900736579502643021513617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10401964212007048057369645 3900736579502643021513617)
                    ·
                      refine ⟨2925552434626982266135213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3900736579502643021513617 2925552434626982266135213)
                      ·
                        rfl

theorem cell23_5697493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_5697493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5697493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5697493 prefixEnd_5697493 := by exact prefixLift 5697493
  have htrace : WordTrace (prefixWord ++ tailWord_5697493) baseStart_5697493 baseEnd_5697493 := by
    simpa [prefixWord, tailWord_5697493, baseEnd_5697493] using wordTrace_append hprefix tailTrace_5697493
  have hstable : (prefixWord ++ tailWord_5697493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5697493).length < 2 ^ (prefixWord ++ tailWord_5697493).sum := by decide
  have hdescent : baseEnd_5697493 < baseStart_5697493 := by decide
  rcases family_descends (prefixWord ++ tailWord_5697493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5697526 : List Nat := [5, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5]
def baseStart_5697526 : Nat := 118140960795 + 5697526 * 2 ^ 59
def prefixEnd_5697526 : Nat := 4983230072969 + 3 ^ 40 * 5697526 * 2
def baseEnd_5697526 : Nat := 2925569379488580637022561

theorem tailTrace_5697526 : CollatzResearch.WordTrace tailWord_5697526 prefixEnd_5697526 2925569379488580637022561 := by
  unfold tailWord_5697526
  simp only [CollatzResearch.WordTrace]
  refine ⟨12987865322302739801040527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 138537230104562557877765621 12987865322302739801040527)
  ·
    refine ⟨19481797983454109701560791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12987865322302739801040527 19481797983454109701560791)
    ·
      refine ⟨29222696975181164552341187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19481797983454109701560791 29222696975181164552341187)
      ·
        refine ⟨43834045462771746828511781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29222696975181164552341187 43834045462771746828511781)
        ·
          refine ⟨8218883524269702530345959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43834045462771746828511781 8218883524269702530345959)
          ·
            refine ⟨12328325286404553795518939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8218883524269702530345959 12328325286404553795518939)
            ·
              refine ⟨18492487929606830693278409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12328325286404553795518939 18492487929606830693278409)
              ·
                refine ⟨13869365947205123019958807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18492487929606830693278409 13869365947205123019958807)
                ·
                  refine ⟨20804048920807684529938211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13869365947205123019958807 20804048920807684529938211)
                  ·
                    refine ⟨31206073381211526794907317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20804048920807684529938211 31206073381211526794907317)
                    ·
                      refine ⟨2925569379488580637022561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31206073381211526794907317 2925569379488580637022561)
                      ·
                        rfl

theorem cell23_5697526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_5697526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5697526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5697526 prefixEnd_5697526 := by exact prefixLift 5697526
  have htrace : WordTrace (prefixWord ++ tailWord_5697526) baseStart_5697526 baseEnd_5697526 := by
    simpa [prefixWord, tailWord_5697526, baseEnd_5697526] using wordTrace_append hprefix tailTrace_5697526
  have hstable : (prefixWord ++ tailWord_5697526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5697526).length < 2 ^ (prefixWord ++ tailWord_5697526).sum := by decide
  have hdescent : baseEnd_5697526 < baseStart_5697526 := by decide
  rcases family_descends (prefixWord ++ tailWord_5697526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5697546 : List Nat := [3, 1, 2, 2, 4, 2, 2, 7]
def baseStart_5697546 : Nat := 118140960795 + 5697546 * 2 ^ 59
def prefixEnd_5697546 : Nat := 4983230072969 + 3 ^ 40 * 5697546 * 2
def baseEnd_5697546 : Nat := 108354801818580391065647

theorem tailTrace_5697546 : CollatzResearch.WordTrace tailWord_5697546 prefixEnd_5697546 108354801818580391065647 := by
  unfold tailWord_5697546
  simp only [CollatzResearch.WordTrace]
  refine ⟨51951643654192845058094123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138537716411180920154917661 51951643654192845058094123)
  ·
    refine ⟨77927465481289267587141185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51951643654192845058094123 77927465481289267587141185)
    ·
      refine ⟨58445599110966950690355889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77927465481289267587141185 58445599110966950690355889)
      ·
        refine ⟨43834199333225213017766917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58445599110966950690355889 43834199333225213017766917)
        ·
          refine ⟨8218912374979727440831297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43834199333225213017766917 8218912374979727440831297)
          ·
            refine ⟨6164184281234795580623473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8218912374979727440831297 6164184281234795580623473)
            ·
              refine ⟨4623138210926096685467605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6164184281234795580623473 4623138210926096685467605)
              ·
                refine ⟨108354801818580391065647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4623138210926096685467605 108354801818580391065647)
                ·
                  rfl

theorem cell23_5697546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 7].length) (baseStart_5697546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5697546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5697546 prefixEnd_5697546 := by exact prefixLift 5697546
  have htrace : WordTrace (prefixWord ++ tailWord_5697546) baseStart_5697546 baseEnd_5697546 := by
    simpa [prefixWord, tailWord_5697546, baseEnd_5697546] using wordTrace_append hprefix tailTrace_5697546
  have hstable : (prefixWord ++ tailWord_5697546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5697546).length < 2 ^ (prefixWord ++ tailWord_5697546).sum := by decide
  have hdescent : baseEnd_5697546 < baseStart_5697546 := by decide
  rcases family_descends (prefixWord ++ tailWord_5697546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5697557 : List Nat := [1, 3, 2, 1, 5, 2, 1, 3, 1, 2, 2]
def baseStart_5697557 : Nat := 118140960795 + 5697557 * 2 ^ 59
def prefixEnd_5697557 : Nat := 4983230072969 + 3 ^ 40 * 5697557 * 2
def baseEnd_5697557 : Nat := 2925585297388870015734919

theorem tailTrace_5697557 : CollatzResearch.WordTrace tailWord_5697557 prefixEnd_5697557 2925585297388870015734919 := by
  unfold tailWord_5697557
  simp only [CollatzResearch.WordTrace]
  refine ⟨207806975819731529111026925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138537983879821019407351283 207806975819731529111026925)
  ·
    refine ⟨77927615932399323416635097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207806975819731529111026925 77927615932399323416635097)
    ·
      refine ⟨58445711949299492562476323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77927615932399323416635097 58445711949299492562476323)
      ·
        refine ⟨87668567923949238843714485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58445711949299492562476323 87668567923949238843714485)
        ·
          refine ⟨8218928242870241141598233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 87668567923949238843714485 8218928242870241141598233)
          ·
            refine ⟨6164196182152680856198675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8218928242870241141598233 6164196182152680856198675)
            ·
              refine ⟨9246294273229021284298013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6164196182152680856198675 9246294273229021284298013)
              ·
                refine ⟨3467360352460882981611755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9246294273229021284298013 3467360352460882981611755)
                ·
                  refine ⟨5201040528691324472417633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3467360352460882981611755 5201040528691324472417633)
                  ·
                    refine ⟨3900780396518493354313225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5201040528691324472417633 3900780396518493354313225)
                    ·
                      refine ⟨2925585297388870015734919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3900780396518493354313225 2925585297388870015734919)
                      ·
                        rfl

theorem cell23_5697557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 3, 1, 2, 2].length) (baseStart_5697557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5697557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5697557 prefixEnd_5697557 := by exact prefixLift 5697557
  have htrace : WordTrace (prefixWord ++ tailWord_5697557) baseStart_5697557 baseEnd_5697557 := by
    simpa [prefixWord, tailWord_5697557, baseEnd_5697557] using wordTrace_append hprefix tailTrace_5697557
  have hstable : (prefixWord ++ tailWord_5697557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5697557).length < 2 ^ (prefixWord ++ tailWord_5697557).sum := by decide
  have hdescent : baseEnd_5697557 < baseStart_5697557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5697557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5697579 : List Nat := [1, 1, 1, 1, 2, 1, 4, 1, 5, 4, 2]
def baseStart_5697579 : Nat := 118140960795 + 5697579 * 2 ^ 59
def prefixEnd_5697579 : Nat := 4983230072969 + 3 ^ 40 * 5697579 * 2
def baseEnd_5697579 : Nat := 2925596593963268929659817

theorem tailTrace_5697579 : CollatzResearch.WordTrace tailWord_5697579 prefixEnd_5697579 2925596593963268929659817 := by
  unfold tailWord_5697579
  simp only [CollatzResearch.WordTrace]
  refine ⟨207807778225651826868327791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138538518817101217912218527 207807778225651826868327791)
  ·
    refine ⟨311711667338477740302491687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207807778225651826868327791 311711667338477740302491687)
    ·
      refine ⟨467567501007716610453737531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311711667338477740302491687 467567501007716610453737531)
      ·
        refine ⟨701351251511574915680606297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 467567501007716610453737531 701351251511574915680606297)
        ·
          refine ⟨526013438633681186760454723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 701351251511574915680606297 526013438633681186760454723)
          ·
            refine ⟨789020157950521780140682085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 526013438633681186760454723 789020157950521780140682085)
            ·
              refine ⟨147941279615722833776377891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 789020157950521780140682085 147941279615722833776377891)
              ·
                refine ⟨221911919423584250664566837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147941279615722833776377891 221911919423584250664566837)
                ·
                  refine ⟨20804242445961023499803141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 221911919423584250664566837 20804242445961023499803141)
                  ·
                    refine ⟨3900795458617691906213089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20804242445961023499803141 3900795458617691906213089)
                    ·
                      refine ⟨2925596593963268929659817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3900795458617691906213089 2925596593963268929659817)
                      ·
                        rfl

theorem cell23_5697579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5, 4, 2].length) (baseStart_5697579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5697579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5697579 prefixEnd_5697579 := by exact prefixLift 5697579
  have htrace : WordTrace (prefixWord ++ tailWord_5697579) baseStart_5697579 baseEnd_5697579 := by
    simpa [prefixWord, tailWord_5697579, baseEnd_5697579] using wordTrace_append hprefix tailTrace_5697579
  have hstable : (prefixWord ++ tailWord_5697579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5697579).length < 2 ^ (prefixWord ++ tailWord_5697579).sum := by decide
  have hdescent : baseEnd_5697579 < baseStart_5697579 := by decide
  rcases family_descends (prefixWord ++ tailWord_5697579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5697596 : List Nat := [2, 2, 2, 2, 2, 1, 2, 3, 1, 4, 2]
def baseStart_5697596 : Nat := 118140960795 + 5697596 * 2 ^ 59
def prefixEnd_5697596 : Nat := 4983230072969 + 3 ^ 40 * 5697596 * 2
def baseEnd_5697596 : Nat := 2925605323134395363147239

theorem tailTrace_5697596 : CollatzResearch.WordTrace tailWord_5697596 prefixEnd_5697596 2925605323134395363147239 := by
  unfold tailWord_5697596
  simp only [CollatzResearch.WordTrace]
  refine ⟨103904199133295119385848321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138538932177726825847797761 103904199133295119385848321)
  ·
    refine ⟨77928149349971339539386241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103904199133295119385848321 77928149349971339539386241)
    ·
      refine ⟨58446112012478504654539681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77928149349971339539386241 58446112012478504654539681)
      ·
        refine ⟨43834584009358878490904761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58446112012478504654539681 43834584009358878490904761)
        ·
          refine ⟨32875938007019158868178571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43834584009358878490904761 32875938007019158868178571)
          ·
            refine ⟨49313907010528738302267857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32875938007019158868178571 49313907010528738302267857)
            ·
              refine ⟨36985430257896553726700893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49313907010528738302267857 36985430257896553726700893)
              ·
                refine ⟨13869536346711207647512835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36985430257896553726700893 13869536346711207647512835)
                ·
                  refine ⟨20804304520066811471269253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13869536346711207647512835 20804304520066811471269253)
                  ·
                    refine ⟨3900807097512527150862985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20804304520066811471269253 3900807097512527150862985)
                    ·
                      refine ⟨2925605323134395363147239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3900807097512527150862985 2925605323134395363147239)
                      ·
                        rfl

theorem cell23_5697596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3, 1, 4, 2].length) (baseStart_5697596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5697596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5697596 prefixEnd_5697596 := by exact prefixLift 5697596
  have htrace : WordTrace (prefixWord ++ tailWord_5697596) baseStart_5697596 baseEnd_5697596 := by
    simpa [prefixWord, tailWord_5697596, baseEnd_5697596] using wordTrace_append hprefix tailTrace_5697596
  have hstable : (prefixWord ++ tailWord_5697596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5697596).length < 2 ^ (prefixWord ++ tailWord_5697596).sum := by decide
  have hdescent : baseEnd_5697596 < baseStart_5697596 := by decide
  rcases family_descends (prefixWord ++ tailWord_5697596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5697613 : List Nat := [1, 6, 1, 1, 1, 1, 3, 2, 1, 4, 2]
def baseStart_5697613 : Nat := 118140960795 + 5697613 * 2 ^ 59
def prefixEnd_5697613 : Nat := 4983230072969 + 3 ^ 40 * 5697613 * 2
def baseEnd_5697613 : Nat := 2925614052305521796634661

theorem tailTrace_5697613 : CollatzResearch.WordTrace tailWord_5697613 prefixEnd_5697613 2925614052305521796634661 := by
  unfold tailWord_5697613
  simp only [CollatzResearch.WordTrace]
  refine ⟨207809018307528650675065493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138539345538352433783376995 207809018307528650675065493)
  ·
    refine ⟨9741047733165405500393695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 207809018307528650675065493 9741047733165405500393695)
    ·
      refine ⟨14611571599748108250590543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9741047733165405500393695 14611571599748108250590543)
      ·
        refine ⟨21917357399622162375885815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14611571599748108250590543 21917357399622162375885815)
        ·
          refine ⟨32876036099433243563828723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21917357399622162375885815 32876036099433243563828723)
          ·
            refine ⟨49314054149149865345743085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32876036099433243563828723 49314054149149865345743085)
            ·
              refine ⟨18492770305931199504653657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49314054149149865345743085 18492770305931199504653657)
              ·
                refine ⟨13869577729448399628490243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18492770305931199504653657 13869577729448399628490243)
                ·
                  refine ⟨20804366594172599442735365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13869577729448399628490243 20804366594172599442735365)
                  ·
                    refine ⟨3900818736407362395512881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20804366594172599442735365 3900818736407362395512881)
                    ·
                      refine ⟨2925614052305521796634661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3900818736407362395512881 2925614052305521796634661)
                      ·
                        rfl

theorem cell23_5697613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_5697613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5697613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5697613 prefixEnd_5697613 := by exact prefixLift 5697613
  have htrace : WordTrace (prefixWord ++ tailWord_5697613) baseStart_5697613 baseEnd_5697613 := by
    simpa [prefixWord, tailWord_5697613, baseEnd_5697613] using wordTrace_append hprefix tailTrace_5697613
  have hstable : (prefixWord ++ tailWord_5697613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5697613).length < 2 ^ (prefixWord ++ tailWord_5697613).sum := by decide
  have hdescent : baseEnd_5697613 < baseStart_5697613 := by decide
  rcases family_descends (prefixWord ++ tailWord_5697613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5697646 : List Nat := [4, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3]
def baseStart_5697646 : Nat := 118140960795 + 5697646 * 2 ^ 59
def prefixEnd_5697646 : Nat := 4983230072969 + 3 ^ 40 * 5697646 * 2
def baseEnd_5697646 : Nat := 2925630997167120167522009

theorem tailTrace_5697646 : CollatzResearch.WordTrace tailWord_5697646 prefixEnd_5697646 2925630997167120167522009 := by
  unfold tailWord_5697646
  simp only [CollatzResearch.WordTrace]
  refine ⟨25976277739551137163877099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138540147944272731540677861 25976277739551137163877099)
  ·
    refine ⟨38964416609326705745815649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25976277739551137163877099 38964416609326705745815649)
    ·
      refine ⟨29223312456995029309361737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38964416609326705745815649 29223312456995029309361737)
      ·
        refine ⟨21917484342746271982021303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29223312456995029309361737 21917484342746271982021303)
        ·
          refine ⟨32876226514119407973031955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21917484342746271982021303 32876226514119407973031955)
          ·
            refine ⟨49314339771179111959547933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32876226514119407973031955 49314339771179111959547933)
            ·
              refine ⟨18492877414192166984830475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49314339771179111959547933 18492877414192166984830475)
              ·
                refine ⟨27739316121288250477245713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18492877414192166984830475 27739316121288250477245713)
                ·
                  refine ⟨20804487090966187857934285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27739316121288250477245713 20804487090966187857934285)
                  ·
                    refine ⟨7801682659112320446725357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20804487090966187857934285 7801682659112320446725357)
                    ·
                      refine ⟨2925630997167120167522009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7801682659112320446725357 2925630997167120167522009)
                      ·
                        rfl

theorem cell23_5697646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_5697646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5697646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5697646 prefixEnd_5697646 := by exact prefixLift 5697646
  have htrace : WordTrace (prefixWord ++ tailWord_5697646) baseStart_5697646 baseEnd_5697646 := by
    simpa [prefixWord, tailWord_5697646, baseEnd_5697646] using wordTrace_append hprefix tailTrace_5697646
  have hstable : (prefixWord ++ tailWord_5697646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5697646).length < 2 ^ (prefixWord ++ tailWord_5697646).sum := by decide
  have hdescent : baseEnd_5697646 < baseStart_5697646 := by decide
  rcases family_descends (prefixWord ++ tailWord_5697646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5697696 : List Nat := [2, 1, 1, 4, 2, 2, 1, 3, 3, 4]
def baseStart_5697696 : Nat := 118140960795 + 5697696 * 2 ^ 59
def prefixEnd_5697696 : Nat := 4983230072969 + 3 ^ 40 * 5697696 * 2
def baseEnd_5697696 : Nat := 975218890399948323965593

theorem tailTrace_5697696 : CollatzResearch.WordTrace tailWord_5697696 prefixEnd_5697696 975218890399948323965593 := by
  unfold tailWord_5697696
  simp only [CollatzResearch.WordTrace]
  refine ⟨103906022783113977925168471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138541363710818637233557961 103906022783113977925168471)
  ·
    refine ⟨155859034174670966887752707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103906022783113977925168471 155859034174670966887752707)
    ·
      refine ⟨233788551262006450331629061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155859034174670966887752707 233788551262006450331629061)
      ·
        refine ⟨43835353361626209437180449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 233788551262006450331629061 43835353361626209437180449)
        ·
          refine ⟨32876515021219657077885337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43835353361626209437180449 32876515021219657077885337)
          ·
            refine ⟨24657386265914742808414003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32876515021219657077885337 24657386265914742808414003)
            ·
              refine ⟨36986079398872114212621005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24657386265914742808414003 36986079398872114212621005)
              ·
                refine ⟨13869779774577042829732877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36986079398872114212621005 13869779774577042829732877)
                ·
                  refine ⟨5201167415466391061149829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13869779774577042829732877 5201167415466391061149829)
                  ·
                    refine ⟨975218890399948323965593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5201167415466391061149829 975218890399948323965593)
                    ·
                      rfl

theorem cell23_5697696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3, 3, 4].length) (baseStart_5697696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5697696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5697696 prefixEnd_5697696 := by exact prefixLift 5697696
  have htrace : WordTrace (prefixWord ++ tailWord_5697696) baseStart_5697696 baseEnd_5697696 := by
    simpa [prefixWord, tailWord_5697696, baseEnd_5697696] using wordTrace_append hprefix tailTrace_5697696
  have hstable : (prefixWord ++ tailWord_5697696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5697696).length < 2 ^ (prefixWord ++ tailWord_5697696).sum := by decide
  have hdescent : baseEnd_5697696 < baseStart_5697696 := by decide
  rcases family_descends (prefixWord ++ tailWord_5697696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5697740 : List Nat := [2, 2, 1, 6, 1, 1, 1, 2, 2, 2, 3]
def baseStart_5697740 : Nat := 118140960795 + 5697740 * 2 ^ 59
def prefixEnd_5697740 : Nat := 4983230072969 + 3 ^ 40 * 5697740 * 2
def baseEnd_5697740 : Nat := 2925679264348642799746577

theorem tailTrace_5697740 : CollatzResearch.WordTrace tailWord_5697740 prefixEnd_5697740 2925679264348642799746577 := by
  unfold tailWord_5697740
  simp only [CollatzResearch.WordTrace]
  refine ⟨103906825189034275682469337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138542433585379034243292449 103906825189034275682469337)
  ·
    refine ⟨77930118891775706761852003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103906825189034275682469337 77930118891775706761852003)
    ·
      refine ⟨116895178337663560142778005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77930118891775706761852003 116895178337663560142778005)
      ·
        refine ⟨5479461484577979381692719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 116895178337663560142778005 5479461484577979381692719)
        ·
          refine ⟨8219192226866969072539079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5479461484577979381692719 8219192226866969072539079)
          ·
            refine ⟨12328788340300453608808619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8219192226866969072539079 12328788340300453608808619)
            ·
              refine ⟨18493182510450680413212929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12328788340300453608808619 18493182510450680413212929)
              ·
                refine ⟨13869886882838010309909697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18493182510450680413212929 13869886882838010309909697)
                ·
                  refine ⟨10402415162128507732432273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13869886882838010309909697 10402415162128507732432273)
                  ·
                    refine ⟨7801811371596380799324205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10402415162128507732432273 7801811371596380799324205)
                    ·
                      refine ⟨2925679264348642799746577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7801811371596380799324205 2925679264348642799746577)
                      ·
                        rfl

theorem cell23_5697740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_5697740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5697740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5697740 prefixEnd_5697740 := by exact prefixLift 5697740
  have htrace : WordTrace (prefixWord ++ tailWord_5697740) baseStart_5697740 baseEnd_5697740 := by
    simpa [prefixWord, tailWord_5697740, baseEnd_5697740] using wordTrace_append hprefix tailTrace_5697740
  have hstable : (prefixWord ++ tailWord_5697740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5697740).length < 2 ^ (prefixWord ++ tailWord_5697740).sum := by decide
  have hdescent : baseEnd_5697740 < baseStart_5697740 := by decide
  rcases family_descends (prefixWord ++ tailWord_5697740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5697753 : List Nat := [1, 2, 1, 2, 3, 1, 5, 1, 3, 1, 3]
def baseStart_5697753 : Nat := 118140960795 + 5697753 * 2 ^ 59
def prefixEnd_5697753 : Nat := 4983230072969 + 3 ^ 40 * 5697753 * 2
def baseEnd_5697753 : Nat := 2925685939597151248884017

theorem tailTrace_5697753 : CollatzResearch.WordTrace tailWord_5697753 prefixEnd_5697753 2925685939597151248884017 := by
  unfold tailWord_5697753
  simp only [CollatzResearch.WordTrace]
  refine ⟨207814124527021454585161913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138542749684680969723441275 207814124527021454585161913)
  ·
    refine ⟨155860593395266090938871435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207814124527021454585161913 155860593395266090938871435)
    ·
      refine ⟨233790890092899136408307153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155860593395266090938871435 233790890092899136408307153)
      ·
        refine ⟨175343167569674352306230365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233790890092899136408307153 175343167569674352306230365)
        ·
          refine ⟨65753687838627882114836387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175343167569674352306230365 65753687838627882114836387)
          ·
            refine ⟨98630531757941823172254581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65753687838627882114836387 98630531757941823172254581)
            ·
              refine ⟨9246612352307045922398867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 98630531757941823172254581 9246612352307045922398867)
              ·
                refine ⟨13869918528460568883598301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9246612352307045922398867 13869918528460568883598301)
                ·
                  refine ⟨5201219448172713331349363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13869918528460568883598301 5201219448172713331349363)
                  ·
                    refine ⟨7801829172259069997024045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5201219448172713331349363 7801829172259069997024045)
                    ·
                      refine ⟨2925685939597151248884017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7801829172259069997024045 2925685939597151248884017)
                      ·
                        rfl

theorem cell23_5697753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 1, 3, 1, 3].length) (baseStart_5697753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5697753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5697753 prefixEnd_5697753 := by exact prefixLift 5697753
  have htrace : WordTrace (prefixWord ++ tailWord_5697753) baseStart_5697753 baseEnd_5697753 := by
    simpa [prefixWord, tailWord_5697753, baseEnd_5697753] using wordTrace_append hprefix tailTrace_5697753
  have hstable : (prefixWord ++ tailWord_5697753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5697753).length < 2 ^ (prefixWord ++ tailWord_5697753).sum := by decide
  have hdescent : baseEnd_5697753 < baseStart_5697753 := by decide
  rcases family_descends (prefixWord ++ tailWord_5697753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5697759 : List Nat := [1, 1, 2, 3, 2, 1, 1, 1, 2, 5, 4]
def baseStart_5697759 : Nat := 118140960795 + 5697759 * 2 ^ 59
def prefixEnd_5697759 : Nat := 4983230072969 + 3 ^ 40 * 5697759 * 2
def baseEnd_5697759 : Nat := 2925689020481078225408989

theorem tailTrace_5697759 : CollatzResearch.WordTrace tailWord_5697759 prefixEnd_5697759 2925689020481078225408989 := by
  unfold tailWord_5697759
  simp only [CollatzResearch.WordTrace]
  refine ⟨207814343364999717609880331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138542895576666478406586887 207814343364999717609880331)
  ·
    refine ⟨311721515047499576414820497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207814343364999717609880331 311721515047499576414820497)
    ·
      refine ⟨233791136285624682311115373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311721515047499576414820497 233791136285624682311115373)
      ·
        refine ⟨87671676107109255866668265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 233791136285624682311115373 87671676107109255866668265)
        ·
          refine ⟨65753757080331941900001199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87671676107109255866668265 65753757080331941900001199)
          ·
            refine ⟨98630635620497912850001799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65753757080331941900001199 98630635620497912850001799)
            ·
              refine ⟨147945953430746869275002699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98630635620497912850001799 147945953430746869275002699)
              ·
                refine ⟨221918930146120303912504049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147945953430746869275002699 221918930146120303912504049)
                ·
                  refine ⟨166439197609590227934378037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 221918930146120303912504049 166439197609590227934378037)
                  ·
                    refine ⟨15603674775899083868847941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 166439197609590227934378037 15603674775899083868847941)
                    ·
                      refine ⟨2925689020481078225408989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15603674775899083868847941 2925689020481078225408989)
                      ·
                        rfl

theorem cell23_5697759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_5697759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5697759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5697759 prefixEnd_5697759 := by exact prefixLift 5697759
  have htrace : WordTrace (prefixWord ++ tailWord_5697759) baseStart_5697759 baseEnd_5697759 := by
    simpa [prefixWord, tailWord_5697759, baseEnd_5697759] using wordTrace_append hprefix tailTrace_5697759
  have hstable : (prefixWord ++ tailWord_5697759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5697759).length < 2 ^ (prefixWord ++ tailWord_5697759).sum := by decide
  have hdescent : baseEnd_5697759 < baseStart_5697759 := by decide
  rcases family_descends (prefixWord ++ tailWord_5697759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5697773 : List Nat := [1, 5, 1, 2, 3, 1, 1, 1, 3, 5]
def baseStart_5697773 : Nat := 118140960795 + 5697773 * 2 ^ 59
def prefixEnd_5697773 : Nat := 4983230072969 + 3 ^ 40 * 5697773 * 2
def baseEnd_5697773 : Nat := 975232069736747056877975

theorem tailTrace_5697773 : CollatzResearch.WordTrace tailWord_5697773 prefixEnd_5697773 975232069736747056877975 := by
  unfold tailWord_5697773
  simp only [CollatzResearch.WordTrace]
  refine ⟨207814853986948998000889973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138543235991299332000593315 207814853986948998000889973)
  ·
    refine ⟨19482642561276468562583435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 207814853986948998000889973 19482642561276468562583435)
    ·
      refine ⟨29223963841914702843875153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19482642561276468562583435 29223963841914702843875153)
      ·
        refine ⟨21917972881436027132906365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29223963841914702843875153 21917972881436027132906365)
        ·
          refine ⟨8219239830538510174839887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21917972881436027132906365 8219239830538510174839887)
          ·
            refine ⟨12328859745807765262259831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8219239830538510174839887 12328859745807765262259831)
            ·
              refine ⟨18493289618711647893389747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12328859745807765262259831 18493289618711647893389747)
              ·
                refine ⟨27739934428067471840084621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18493289618711647893389747 27739934428067471840084621)
                ·
                  refine ⟨10402475410525301940031733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27739934428067471840084621 10402475410525301940031733)
                  ·
                    refine ⟨975232069736747056877975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10402475410525301940031733 975232069736747056877975)
                    ·
                      rfl

theorem cell23_5697773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_5697773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5697773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5697773 prefixEnd_5697773 := by exact prefixLift 5697773
  have htrace : WordTrace (prefixWord ++ tailWord_5697773) baseStart_5697773 baseEnd_5697773 := by
    simpa [prefixWord, tailWord_5697773, baseEnd_5697773] using wordTrace_append hprefix tailTrace_5697773
  have hstable : (prefixWord ++ tailWord_5697773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5697773).length < 2 ^ (prefixWord ++ tailWord_5697773).sum := by decide
  have hdescent : baseEnd_5697773 < baseStart_5697773 := by decide
  rcases family_descends (prefixWord ++ tailWord_5697773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5697776 : List Nat := [2, 1, 1, 1, 3, 1, 1, 3, 2, 6, 2]
def baseStart_5697776 : Nat := 118140960795 + 5697776 * 2 ^ 59
def prefixEnd_5697776 : Nat := 4983230072969 + 3 ^ 40 * 5697776 * 2
def baseEnd_5697776 : Nat := 2925697749652204658896411

theorem tailTrace_5697776 : CollatzResearch.WordTrace tailWord_5697776 prefixEnd_5697776 2925697749652204658896411 := by
  unfold tailWord_5697776
  simp only [CollatzResearch.WordTrace]
  refine ⟨103907481702969064756624591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138543308937292086342166121 103907481702969064756624591)
  ·
    refine ⟨155861222554453597134936887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103907481702969064756624591 155861222554453597134936887)
    ·
      refine ⟨233791833831680395702405331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155861222554453597134936887 233791833831680395702405331)
      ·
        refine ⟨350687750747520593553607997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233791833831680395702405331 350687750747520593553607997)
        ·
          refine ⟨131507906530320222582602999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 350687750747520593553607997 131507906530320222582602999)
          ·
            refine ⟨197261859795480333873904499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131507906530320222582602999 197261859795480333873904499)
            ·
              refine ⟨295892789693220500810856749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197261859795480333873904499 295892789693220500810856749)
              ·
                refine ⟨110959796134957687804071281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 295892789693220500810856749 110959796134957687804071281)
                ·
                  refine ⟨83219847101218265853053461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110959796134957687804071281 83219847101218265853053461)
                  ·
                    refine ⟨3900930332869606211861881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 83219847101218265853053461 3900930332869606211861881)
                    ·
                      refine ⟨2925697749652204658896411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3900930332869606211861881 2925697749652204658896411)
                      ·
                        rfl

theorem cell23_5697776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 2, 6, 2].length) (baseStart_5697776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5697776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5697776 prefixEnd_5697776 := by exact prefixLift 5697776
  have htrace : WordTrace (prefixWord ++ tailWord_5697776) baseStart_5697776 baseEnd_5697776 := by
    simpa [prefixWord, tailWord_5697776, baseEnd_5697776] using wordTrace_append hprefix tailTrace_5697776
  have hstable : (prefixWord ++ tailWord_5697776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5697776).length < 2 ^ (prefixWord ++ tailWord_5697776).sum := by decide
  have hdescent : baseEnd_5697776 < baseStart_5697776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5697776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5697786 : List Nat := [3, 1, 1, 1, 1, 6, 1, 2, 1, 6]
def baseStart_5697786 : Nat := 118140960795 + 5697786 * 2 ^ 59
def prefixEnd_5697786 : Nat := 4983230072969 + 3 ^ 40 * 5697786 * 2
def baseEnd_5697786 : Nat := 975234294819583206590455

theorem tailTrace_5697786 : CollatzResearch.WordTrace tailWord_5697786 prefixEnd_5697786 975234294819583206590455 := by
  unfold tailWord_5697786
  simp only [CollatzResearch.WordTrace]
  refine ⟨51953832033975475305278303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138543552090601267480742141 51953832033975475305278303)
  ·
    refine ⟨77930748050963212957917455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51953832033975475305278303 77930748050963212957917455)
    ·
      refine ⟨116896122076444819436876183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77930748050963212957917455 116896122076444819436876183)
      ·
        refine ⟨175344183114667229155314275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116896122076444819436876183 175344183114667229155314275)
        ·
          refine ⟨263016274672000843732971413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175344183114667229155314275 263016274672000843732971413)
          ·
            refine ⟨12328887875250039549983035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 263016274672000843732971413 12328887875250039549983035)
            ·
              refine ⟨18493331812875059324974553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12328887875250039549983035 18493331812875059324974553)
              ·
                refine ⟨13869998859656294493730915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18493331812875059324974553 13869998859656294493730915)
                ·
                  refine ⟨20804998289484441740596373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13869998859656294493730915 20804998289484441740596373)
                  ·
                    refine ⟨975234294819583206590455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20804998289484441740596373 975234294819583206590455)
                    ·
                      rfl

theorem cell23_5697786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 2, 1, 6].length) (baseStart_5697786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5697786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5697786 prefixEnd_5697786 := by exact prefixLift 5697786
  have htrace : WordTrace (prefixWord ++ tailWord_5697786) baseStart_5697786 baseEnd_5697786 := by
    simpa [prefixWord, tailWord_5697786, baseEnd_5697786] using wordTrace_append hprefix tailTrace_5697786
  have hstable : (prefixWord ++ tailWord_5697786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5697786).length < 2 ^ (prefixWord ++ tailWord_5697786).sum := by decide
  have hdescent : baseEnd_5697786 < baseStart_5697786 := by decide
  rcases family_descends (prefixWord ++ tailWord_5697786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5697790 : List Nat := [4, 2, 2, 1, 1, 1, 5, 1, 1, 5]
def baseStart_5697790 : Nat := 118140960795 + 5697790 * 2 ^ 59
def prefixEnd_5697790 : Nat := 4983230072969 + 3 ^ 40 * 5697790 * 2
def baseEnd_5697790 : Nat := 975234979460455868040449

theorem tailTrace_5697790 : CollatzResearch.WordTrace tailWord_5697790 prefixEnd_5697790 975234979460455868040449 := by
  unfold tailWord_5697790
  simp only [CollatzResearch.WordTrace]
  refine ⟨25976934253485926238032353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138543649351924939936172549 25976934253485926238032353)
  ·
    refine ⟨19482700690114444678524265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25976934253485926238032353 19482700690114444678524265)
    ·
      refine ⟨14612025517585833508893199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19482700690114444678524265 14612025517585833508893199)
      ·
        refine ⟨21918038276378750263339799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14612025517585833508893199 21918038276378750263339799)
        ·
          refine ⟨32877057414568125395009699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21918038276378750263339799 32877057414568125395009699)
          ·
            refine ⟨49315586121852188092514549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32877057414568125395009699 49315586121852188092514549)
            ·
              refine ⟨4623336198923642633673239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49315586121852188092514549 4623336198923642633673239)
              ·
                refine ⟨6935004298385463950509859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4623336198923642633673239 6935004298385463950509859)
                ·
                  refine ⟨10402506447578195925764789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6935004298385463950509859 10402506447578195925764789)
                  ·
                    refine ⟨975234979460455868040449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10402506447578195925764789 975234979460455868040449)
                    ·
                      rfl

theorem cell23_5697790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_5697790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5697790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5697790 prefixEnd_5697790 := by exact prefixLift 5697790
  have htrace : WordTrace (prefixWord ++ tailWord_5697790) baseStart_5697790 baseEnd_5697790 := by
    simpa [prefixWord, tailWord_5697790, baseEnd_5697790] using wordTrace_append hprefix tailTrace_5697790
  have hstable : (prefixWord ++ tailWord_5697790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5697790).length < 2 ^ (prefixWord ++ tailWord_5697790).sum := by decide
  have hdescent : baseEnd_5697790 < baseStart_5697790 := by decide
  rcases family_descends (prefixWord ++ tailWord_5697790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5697803 : List Nat := [1, 1, 1, 1, 5, 2, 4, 2, 2, 4]
def baseStart_5697803 : Nat := 118140960795 + 5697803 * 2 ^ 59
def prefixEnd_5697803 : Nat := 4983230072969 + 3 ^ 40 * 5697803 * 2
def baseEnd_5697803 : Nat := 975237204543292017752929

theorem tailTrace_5697803 : CollatzResearch.WordTrace tailWord_5697803 prefixEnd_5697803 975237204543292017752929 := by
  unfold tailWord_5697803
  simp only [CollatzResearch.WordTrace]
  refine ⟨207815948176840313124482063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138543965451226875416321375 207815948176840313124482063)
  ·
    refine ⟨311723922265260469686723095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207815948176840313124482063 311723922265260469686723095)
    ·
      refine ⟨467585883397890704530084643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311723922265260469686723095 467585883397890704530084643)
      ·
        refine ⟨701378825096836056795126965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 467585883397890704530084643 701378825096836056795126965)
        ·
          refine ⟨65754264852828380324543153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 701378825096836056795126965 65754264852828380324543153)
          ·
            refine ⟨49315698639621285243407365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65754264852828380324543153 49315698639621285243407365)
            ·
              refine ⟨9246693494928990983138881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49315698639621285243407365 9246693494928990983138881)
              ·
                refine ⟨6935020121196743237354161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9246693494928990983138881 6935020121196743237354161)
                ·
                  refine ⟨5201265090897557428015621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6935020121196743237354161 5201265090897557428015621)
                  ·
                    refine ⟨975237204543292017752929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5201265090897557428015621 975237204543292017752929)
                    ·
                      rfl

theorem cell23_5697803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 2, 2, 4].length) (baseStart_5697803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5697803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5697803 prefixEnd_5697803 := by exact prefixLift 5697803
  have htrace : WordTrace (prefixWord ++ tailWord_5697803) baseStart_5697803 baseEnd_5697803 := by
    simpa [prefixWord, tailWord_5697803, baseEnd_5697803] using wordTrace_append hprefix tailTrace_5697803
  have hstable : (prefixWord ++ tailWord_5697803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5697803).length < 2 ^ (prefixWord ++ tailWord_5697803).sum := by decide
  have hdescent : baseEnd_5697803 < baseStart_5697803 := by decide
  rcases family_descends (prefixWord ++ tailWord_5697803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5697806 : List Nat := [4, 1, 1, 2, 1, 2, 1, 2, 3, 2, 4]
def baseStart_5697806 : Nat := 118140960795 + 5697806 * 2 ^ 59
def prefixEnd_5697806 : Nat := 4983230072969 + 3 ^ 40 * 5697806 * 2
def baseEnd_5697806 : Nat := 2925713154071839541521273

theorem tailTrace_5697806 : CollatzResearch.WordTrace tailWord_5697806 prefixEnd_5697806 2925713154071839541521273 := by
  unfold tailWord_5697806
  simp only [CollatzResearch.WordTrace]
  refine ⟨25977007199478680579605159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138544038397219629757894181 25977007199478680579605159)
  ·
    refine ⟨38965510799218020869407739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25977007199478680579605159 38965510799218020869407739)
    ·
      refine ⟨58448266198827031304111609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38965510799218020869407739 58448266198827031304111609)
      ·
        refine ⟨43836199649120273478083707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58448266198827031304111609 43836199649120273478083707)
        ·
          refine ⟨65754299473680410217125561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43836199649120273478083707 65754299473680410217125561)
          ·
            refine ⟨49315724605260307662844171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65754299473680410217125561 49315724605260307662844171)
            ·
              refine ⟨73973586907890461494266257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49315724605260307662844171 73973586907890461494266257)
              ·
                refine ⟨55480190180917846120699693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73973586907890461494266257 55480190180917846120699693)
                ·
                  refine ⟨20805071317844192295262385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55480190180917846120699693 20805071317844192295262385)
                  ·
                    refine ⟨15603803488383144221446789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20805071317844192295262385 15603803488383144221446789)
                    ·
                      refine ⟨2925713154071839541521273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15603803488383144221446789 2925713154071839541521273)
                      ·
                        rfl

theorem cell23_5697806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_5697806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5697806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5697806 prefixEnd_5697806 := by exact prefixLift 5697806
  have htrace : WordTrace (prefixWord ++ tailWord_5697806) baseStart_5697806 baseEnd_5697806 := by
    simpa [prefixWord, tailWord_5697806, baseEnd_5697806] using wordTrace_append hprefix tailTrace_5697806
  have hstable : (prefixWord ++ tailWord_5697806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5697806).length < 2 ^ (prefixWord ++ tailWord_5697806).sum := by decide
  have hdescent : baseEnd_5697806 < baseStart_5697806 := by decide
  rcases family_descends (prefixWord ++ tailWord_5697806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5697819 : List Nat := [1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 6]
def baseStart_5697819 : Nat := 118140960795 + 5697819 * 2 ^ 59
def prefixEnd_5697819 : Nat := 4983230072969 + 3 ^ 40 * 5697819 * 2
def baseEnd_5697819 : Nat := 2925719829320347990658713

theorem tailTrace_5697819 : CollatzResearch.WordTrace tailWord_5697819 prefixEnd_5697819 2925719829320347990658713 := by
  unfold tailWord_5697819
  simp only [CollatzResearch.WordTrace]
  refine ⟨207816531744782347857064511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138544354496521565238043007 207816531744782347857064511)
  ·
    refine ⟨311724797617173521785596767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207816531744782347857064511 311724797617173521785596767)
    ·
      refine ⟨467587196425760282678395151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311724797617173521785596767 467587196425760282678395151)
      ·
        refine ⟨701380794638640424017592727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 467587196425760282678395151 701380794638640424017592727)
        ·
          refine ⟨1052071191957960636026389091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 701380794638640424017592727 1052071191957960636026389091)
          ·
            refine ⟨1578106787936940954039583637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1052071191957960636026389091 1578106787936940954039583637)
            ·
              refine ⟨73973755684544107220605483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1578106787936940954039583637 73973755684544107220605483)
              ·
                refine ⟨110960633526816160830908225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73973755684544107220605483 110960633526816160830908225)
                ·
                  refine ⟨83220475145112120623181169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110960633526816160830908225 83220475145112120623181169)
                  ·
                    refine ⟨62415356358834090467385877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 83220475145112120623181169 62415356358834090467385877)
                    ·
                      refine ⟨2925719829320347990658713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62415356358834090467385877 2925719829320347990658713)
                      ·
                        rfl

theorem cell23_5697819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 6].length) (baseStart_5697819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5697819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5697819 prefixEnd_5697819 := by exact prefixLift 5697819
  have htrace : WordTrace (prefixWord ++ tailWord_5697819) baseStart_5697819 baseEnd_5697819 := by
    simpa [prefixWord, tailWord_5697819, baseEnd_5697819] using wordTrace_append hprefix tailTrace_5697819
  have hstable : (prefixWord ++ tailWord_5697819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5697819).length < 2 ^ (prefixWord ++ tailWord_5697819).sum := by decide
  have hdescent : baseEnd_5697819 < baseStart_5697819 := by decide
  rcases family_descends (prefixWord ++ tailWord_5697819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5697823 : List Nat := [1, 1, 2, 4, 3, 2, 2, 1, 1, 2, 4]
def baseStart_5697823 : Nat := 118140960795 + 5697823 * 2 ^ 59
def prefixEnd_5697823 : Nat := 4983230072969 + 3 ^ 40 * 5697823 * 2
def baseEnd_5697823 : Nat := 2925721883242965975008695

theorem tailTrace_5697823 : CollatzResearch.WordTrace tailWord_5697823 prefixEnd_5697823 2925721883242965975008695 := by
  unfold tailWord_5697823
  simp only [CollatzResearch.WordTrace]
  refine ⟨207816677636767856540210123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138544451757845237693473415 207816677636767856540210123)
  ·
    refine ⟨311725016455151784810315185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207816677636767856540210123 311725016455151784810315185)
    ·
      refine ⟨233793762341363838607736389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311725016455151784810315185 233793762341363838607736389)
      ·
        refine ⟨43836330439005719738950573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 233793762341363838607736389 43836330439005719738950573)
        ·
          refine ⟨16438623914627144902106465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43836330439005719738950573 16438623914627144902106465)
          ·
            refine ⟨12328967935970358676579849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16438623914627144902106465 12328967935970358676579849)
            ·
              refine ⟨9246725951977769007434887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12328967935970358676579849 9246725951977769007434887)
              ·
                refine ⟨13870088927966653511152331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9246725951977769007434887 13870088927966653511152331)
                ·
                  refine ⟨20805133391949980266728497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13870088927966653511152331 20805133391949980266728497)
                  ·
                    refine ⟨15603850043962485200046373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20805133391949980266728497 15603850043962485200046373)
                    ·
                      refine ⟨2925721883242965975008695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15603850043962485200046373 2925721883242965975008695)
                      ·
                        rfl

theorem cell23_5697823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_5697823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5697823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5697823 prefixEnd_5697823 := by exact prefixLift 5697823
  have htrace : WordTrace (prefixWord ++ tailWord_5697823) baseStart_5697823 baseEnd_5697823 := by
    simpa [prefixWord, tailWord_5697823, baseEnd_5697823] using wordTrace_append hprefix tailTrace_5697823
  have hstable : (prefixWord ++ tailWord_5697823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5697823).length < 2 ^ (prefixWord ++ tailWord_5697823).sum := by decide
  have hdescent : baseEnd_5697823 < baseStart_5697823 := by decide
  rcases family_descends (prefixWord ++ tailWord_5697823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5697831 : List Nat := [1, 1, 8, 1, 1, 2, 1, 1, 2, 3, 2]
def baseStart_5697831 : Nat := 118140960795 + 5697831 * 2 ^ 59
def prefixEnd_5697831 : Nat := 4983230072969 + 3 ^ 40 * 5697831 * 2
def baseEnd_5697831 : Nat := 2925725991088201943708659

theorem tailTrace_5697831 : CollatzResearch.WordTrace tailWord_5697831 prefixEnd_5697831 2925725991088201943708659 := by
  unfold tailWord_5697831
  simp only [CollatzResearch.WordTrace]
  refine ⟨207816969420738873906501347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138544646280492582604334231 207816969420738873906501347)
  ·
    refine ⟨311725454131108310859752021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207816969420738873906501347 311725454131108310859752021)
    ·
      refine ⟨3653032665598925517887719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 311725454131108310859752021 3653032665598925517887719)
      ·
        refine ⟨5479548998398388276831579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3653032665598925517887719 5479548998398388276831579)
        ·
          refine ⟨8219323497597582415247369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5479548998398388276831579 8219323497597582415247369)
          ·
            refine ⟨6164492623198186811435527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8219323497597582415247369 6164492623198186811435527)
            ·
              refine ⟨9246738934797280217153291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6164492623198186811435527 9246738934797280217153291)
              ·
                refine ⟨13870108402195920325729937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9246738934797280217153291 13870108402195920325729937)
                ·
                  refine ⟨10402581301646940244297453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13870108402195920325729937 10402581301646940244297453)
                  ·
                    refine ⟨3900967988117602591611545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10402581301646940244297453 3900967988117602591611545)
                    ·
                      refine ⟨2925725991088201943708659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3900967988117602591611545 2925725991088201943708659)
                      ·
                        rfl

theorem cell23_5697831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_5697831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5697831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5697831 prefixEnd_5697831 := by exact prefixLift 5697831
  have htrace : WordTrace (prefixWord ++ tailWord_5697831) baseStart_5697831 baseEnd_5697831 := by
    simpa [prefixWord, tailWord_5697831, baseEnd_5697831] using wordTrace_append hprefix tailTrace_5697831
  have hstable : (prefixWord ++ tailWord_5697831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5697831).length < 2 ^ (prefixWord ++ tailWord_5697831).sum := by decide
  have hdescent : baseEnd_5697831 < baseStart_5697831 := by decide
  rcases family_descends (prefixWord ++ tailWord_5697831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5697843 : List Nat := [1, 1, 1, 2, 5, 1, 2, 2, 4, 1, 3]
def baseStart_5697843 : Nat := 118140960795 + 5697843 * 2 ^ 59
def prefixEnd_5697843 : Nat := 4983230072969 + 3 ^ 40 * 5697843 * 2
def baseEnd_5697843 : Nat := 2925732152856055896758603

theorem tailTrace_5697843 : CollatzResearch.WordTrace tailWord_5697843 prefixEnd_5697843 2925732152856055896758603 := by
  unfold tailWord_5697843
  simp only [CollatzResearch.WordTrace]
  refine ⟨207817407096695399955938183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138544938064463599970625455 207817407096695399955938183)
  ·
    refine ⟨311726110645043099933907275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207817407096695399955938183 311726110645043099933907275)
    ·
      refine ⟨467589165967564649900860913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311726110645043099933907275 467589165967564649900860913)
      ·
        refine ⟨350691874475673487425645685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 467589165967564649900860913 350691874475673487425645685)
        ·
          refine ⟨32877363232094389446154283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 350691874475673487425645685 32877363232094389446154283)
          ·
            refine ⟨49316044848141584169231425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32877363232094389446154283 49316044848141584169231425)
            ·
              refine ⟨36987033636106188126923569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49316044848141584169231425 36987033636106188126923569)
              ·
                refine ⟨27740275227079641095192677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36987033636106188126923569 27740275227079641095192677)
                ·
                  refine ⟨5201301605077432705348627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27740275227079641095192677 5201301605077432705348627)
                  ·
                    refine ⟨7801952407616149058022941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5201301605077432705348627 7801952407616149058022941)
                    ·
                      refine ⟨2925732152856055896758603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7801952407616149058022941 2925732152856055896758603)
                      ·
                        rfl

theorem cell23_5697843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 4, 1, 3].length) (baseStart_5697843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5697843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5697843 prefixEnd_5697843 := by exact prefixLift 5697843
  have htrace : WordTrace (prefixWord ++ tailWord_5697843) baseStart_5697843 baseEnd_5697843 := by
    simpa [prefixWord, tailWord_5697843, baseEnd_5697843] using wordTrace_append hprefix tailTrace_5697843
  have hstable : (prefixWord ++ tailWord_5697843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5697843).length < 2 ^ (prefixWord ++ tailWord_5697843).sum := by decide
  have hdescent : baseEnd_5697843 < baseStart_5697843 := by decide
  rcases family_descends (prefixWord ++ tailWord_5697843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5697844 : List Nat := [2, 5, 1, 1, 1, 2, 1, 5, 1, 2, 2]
def baseStart_5697844 : Nat := 118140960795 + 5697844 * 2 ^ 59
def prefixEnd_5697844 : Nat := 4983230072969 + 3 ^ 40 * 5697844 * 2
def baseEnd_5697844 : Nat := 2925732666336710392846099

theorem tailTrace_5697844 : CollatzResearch.WordTrace tailWord_5697844 prefixEnd_5697844 2925732666336710392846099 := by
  unfold tailWord_5697844
  simp only [CollatzResearch.WordTrace]
  refine ⟨103908721784845888563362293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138544962379794518084483057 103908721784845888563362293)
  ·
    refine ⟨9741442667329302052815215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 103908721784845888563362293 9741442667329302052815215)
    ·
      refine ⟨14612164000993953079222823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9741442667329302052815215 14612164000993953079222823)
      ·
        refine ⟨21918246001490929618834235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14612164000993953079222823 21918246001490929618834235)
        ·
          refine ⟨32877369002236394428251353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21918246001490929618834235 32877369002236394428251353)
          ·
            refine ⟨24658026751677295821188515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32877369002236394428251353 24658026751677295821188515)
            ·
              refine ⟨36987040127515943731782773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24658026751677295821188515 36987040127515943731782773)
              ·
                refine ⟨3467535011954619724854635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36987040127515943731782773 3467535011954619724854635)
                ·
                  refine ⟨5201302517931929587281953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3467535011954619724854635 5201302517931929587281953)
                  ·
                    refine ⟨3900976888448947190461465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5201302517931929587281953 3900976888448947190461465)
                    ·
                      refine ⟨2925732666336710392846099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3900976888448947190461465 2925732666336710392846099)
                      ·
                        rfl

theorem cell23_5697844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_5697844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5697844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5697844 prefixEnd_5697844 := by exact prefixLift 5697844
  have htrace : WordTrace (prefixWord ++ tailWord_5697844) baseStart_5697844 baseEnd_5697844 := by
    simpa [prefixWord, tailWord_5697844, baseEnd_5697844] using wordTrace_append hprefix tailTrace_5697844
  have hstable : (prefixWord ++ tailWord_5697844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5697844).length < 2 ^ (prefixWord ++ tailWord_5697844).sum := by decide
  have hdescent : baseEnd_5697844 < baseStart_5697844 := by decide
  rcases family_descends (prefixWord ++ tailWord_5697844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5697877 : List Nat := [1, 3, 2, 2, 5, 1, 1, 1, 1, 3, 3]
def baseStart_5697877 : Nat := 118140960795 + 5697877 * 2 ^ 59
def prefixEnd_5697877 : Nat := 4983230072969 + 3 ^ 40 * 5697877 * 2
def baseEnd_5697877 : Nat := 2925749611198308763733447

theorem tailTrace_5697877 : CollatzResearch.WordTrace tailWord_5697877 prefixEnd_5697877 2925749611198308763733447 := by
  unfold tailWord_5697877
  simp only [CollatzResearch.WordTrace]
  refine ⟨207818647178572223762675885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138545764785714815841783923 207818647178572223762675885)
  ·
    refine ⟨77931992691964583911003457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207818647178572223762675885 77931992691964583911003457)
    ·
      refine ⟨58448994518973437933252593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77931992691964583911003457 58448994518973437933252593)
      ·
        refine ⟨43836745889230078449939445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58448994518973437933252593 43836745889230078449939445)
        ·
          refine ⟨4109694927115319854681823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43836745889230078449939445 4109694927115319854681823)
          ·
            refine ⟨6164542390672979782022735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4109694927115319854681823 6164542390672979782022735)
            ·
              refine ⟨9246813586009469673034103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6164542390672979782022735 9246813586009469673034103)
              ·
                refine ⟨13870220379014204509551155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9246813586009469673034103 13870220379014204509551155)
                ·
                  refine ⟨20805330568521306764326733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13870220379014204509551155 20805330568521306764326733)
                  ·
                    refine ⟨7801998963195490036622525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20805330568521306764326733 7801998963195490036622525)
                    ·
                      refine ⟨2925749611198308763733447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7801998963195490036622525 2925749611198308763733447)
                      ·
                        rfl

theorem cell23_5697877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 1, 1, 3, 3].length) (baseStart_5697877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5697877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5697877 prefixEnd_5697877 := by exact prefixLift 5697877
  have htrace : WordTrace (prefixWord ++ tailWord_5697877) baseStart_5697877 baseEnd_5697877 := by
    simpa [prefixWord, tailWord_5697877, baseEnd_5697877] using wordTrace_append hprefix tailTrace_5697877
  have hstable : (prefixWord ++ tailWord_5697877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5697877).length < 2 ^ (prefixWord ++ tailWord_5697877).sum := by decide
  have hdescent : baseEnd_5697877 < baseStart_5697877 := by decide
  rcases family_descends (prefixWord ++ tailWord_5697877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5697934 : List Nat := [4, 1, 1, 4, 1, 2, 1, 3, 2, 2, 2]
def baseStart_5697934 : Nat := 118140960795 + 5697934 * 2 ^ 59
def prefixEnd_5697934 : Nat := 4983230072969 + 3 ^ 40 * 5697934 * 2
def baseEnd_5697934 : Nat := 2925778879595615040720685

theorem tailTrace_5697934 : CollatzResearch.WordTrace tailWord_5697934 prefixEnd_5697934 2925778879595615040720685 := by
  unfold tailWord_5697934
  simp only [CollatzResearch.WordTrace]
  refine ⟨25977590767420715312187607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138547150759577148331667237 25977590767420715312187607)
  ·
    refine ⟨38966386151131072968281411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25977590767420715312187607 38966386151131072968281411)
    ·
      refine ⟨58449579226696609452422117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38966386151131072968281411 58449579226696609452422117)
      ·
        refine ⟨10959296105005614272329147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58449579226696609452422117 10959296105005614272329147)
        ·
          refine ⟨16438944157508421408493721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10959296105005614272329147 16438944157508421408493721)
          ·
            refine ⟨12329208118131316056370291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16438944157508421408493721 12329208118131316056370291)
            ·
              refine ⟨18493812177196974084555437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12329208118131316056370291 18493812177196974084555437)
              ·
                refine ⟨6935179566448865281708289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18493812177196974084555437 6935179566448865281708289)
                ·
                  refine ⟨5201384674836648961281217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6935179566448865281708289 5201384674836648961281217)
                  ·
                    refine ⟨3901038506127486720960913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5201384674836648961281217 3901038506127486720960913)
                    ·
                      refine ⟨2925778879595615040720685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3901038506127486720960913 2925778879595615040720685)
                      ·
                        rfl

theorem cell23_5697934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_5697934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5697934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5697934 prefixEnd_5697934 := by exact prefixLift 5697934
  have htrace : WordTrace (prefixWord ++ tailWord_5697934) baseStart_5697934 baseEnd_5697934 := by
    simpa [prefixWord, tailWord_5697934, baseEnd_5697934] using wordTrace_append hprefix tailTrace_5697934
  have hstable : (prefixWord ++ tailWord_5697934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5697934).length < 2 ^ (prefixWord ++ tailWord_5697934).sum := by decide
  have hdescent : baseEnd_5697934 < baseStart_5697934 := by decide
  rcases family_descends (prefixWord ++ tailWord_5697934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5697976 : List Nat := [2, 1, 2, 1, 2, 2, 1, 1, 1, 5, 5]
def baseStart_5697976 : Nat := 118140960795 + 5697976 * 2 ^ 59
def prefixEnd_5697976 : Nat := 4983230072969 + 3 ^ 40 * 5697976 * 2
def baseEnd_5697976 : Nat := 2925800445783103876395491

theorem tailTrace_5697976 : CollatzResearch.WordTrace tailWord_5697976 prefixEnd_5697976 2925800445783103876395491 := by
  unfold tailWord_5697976
  simp only [CollatzResearch.WordTrace]
  refine ⟨103911129002606781835264891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138548172003475709113686521 103911129002606781835264891)
  ·
    refine ⟨155866693503910172752897337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103911129002606781835264891 155866693503910172752897337)
    ·
      refine ⟨116900020127932629564673003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155866693503910172752897337 116900020127932629564673003)
      ·
        refine ⟨175350030191898944347009505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116900020127932629564673003 175350030191898944347009505)
        ·
          refine ⟨131512522643924208260257129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175350030191898944347009505 131512522643924208260257129)
          ·
            refine ⟨98634391982943156195192847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131512522643924208260257129 98634391982943156195192847)
            ·
              refine ⟨147951587974414734292789271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98634391982943156195192847 147951587974414734292789271)
              ·
                refine ⟨221927381961622101439183907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147951587974414734292789271 221927381961622101439183907)
                ·
                  refine ⟨332891072942433152158775861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 221927381961622101439183907 332891072942433152158775861)
                  ·
                    refine ⟨31208538088353108014885237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 332891072942433152158775861 31208538088353108014885237)
                    ·
                      refine ⟨2925800445783103876395491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31208538088353108014885237 2925800445783103876395491)
                      ·
                        rfl

theorem cell23_5697976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 1, 5, 5].length) (baseStart_5697976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5697976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5697976 prefixEnd_5697976 := by exact prefixLift 5697976
  have htrace : WordTrace (prefixWord ++ tailWord_5697976) baseStart_5697976 baseEnd_5697976 := by
    simpa [prefixWord, tailWord_5697976, baseEnd_5697976] using wordTrace_append hprefix tailTrace_5697976
  have hstable : (prefixWord ++ tailWord_5697976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5697976).length < 2 ^ (prefixWord ++ tailWord_5697976).sum := by decide
  have hdescent : baseEnd_5697976 < baseStart_5697976 := by decide
  rcases family_descends (prefixWord ++ tailWord_5697976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5697993 : List Nat := [1, 2, 1, 1, 2, 1, 4, 2, 4, 2, 3]
def baseStart_5697993 : Nat := 118140960795 + 5697993 * 2 ^ 59
def prefixEnd_5697993 : Nat := 4983230072969 + 3 ^ 40 * 5697993 * 2
def baseEnd_5697993 : Nat := 2925809174954230309882913

theorem tailTrace_5697993 : CollatzResearch.WordTrace tailWord_5697993 prefixEnd_5697993 2925809174954230309882913 := by
  unfold tailWord_5697993
  simp only [CollatzResearch.WordTrace]
  refine ⟨207822878046151975573898633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138548585364101317049265755 207822878046151975573898633)
  ·
    refine ⟨155867158534613981680423975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207822878046151975573898633 155867158534613981680423975)
    ·
      refine ⟨233800737801920972520635963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155867158534613981680423975 233800737801920972520635963)
      ·
        refine ⟨350701106702881458780953945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233800737801920972520635963 350701106702881458780953945)
        ·
          refine ⟨263025830027161094085715459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 350701106702881458780953945 263025830027161094085715459)
          ·
            refine ⟨394538745040741641128573189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263025830027161094085715459 394538745040741641128573189)
            ·
              refine ⟨73976014695139057711607473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 394538745040741641128573189 73976014695139057711607473)
              ·
                refine ⟨55482011021354293283705605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73976014695139057711607473 55482011021354293283705605)
                ·
                  refine ⟨10402877066503929990694801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55482011021354293283705605 10402877066503929990694801)
                  ·
                    refine ⟨7802157799877947493021101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10402877066503929990694801 7802157799877947493021101)
                    ·
                      refine ⟨2925809174954230309882913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7802157799877947493021101 2925809174954230309882913)
                      ·
                        rfl

theorem cell23_5697993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 4, 2, 3].length) (baseStart_5697993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5697993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5697993 prefixEnd_5697993 := by exact prefixLift 5697993
  have htrace : WordTrace (prefixWord ++ tailWord_5697993) baseStart_5697993 baseEnd_5697993 := by
    simpa [prefixWord, tailWord_5697993, baseEnd_5697993] using wordTrace_append hprefix tailTrace_5697993
  have hstable : (prefixWord ++ tailWord_5697993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5697993).length < 2 ^ (prefixWord ++ tailWord_5697993).sum := by decide
  have hdescent : baseEnd_5697993 < baseStart_5697993 := by decide
  rcases family_descends (prefixWord ++ tailWord_5697993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5698013 : List Nat := [1, 4, 3, 1, 1, 1, 2, 2, 8]
def baseStart_5698013 : Nat := 118140960795 + 5698013 * 2 ^ 59
def prefixEnd_5698013 : Nat := 4983230072969 + 3 ^ 40 * 5698013 * 2
def baseEnd_5698013 : Nat := 325091049396368914625869

theorem tailTrace_5698013 : CollatzResearch.WordTrace tailWord_5698013 prefixEnd_5698013 325091049396368914625869 := by
  unfold tailWord_5698013
  simp only [CollatzResearch.WordTrace]
  refine ⟨207823607506079518989626693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138549071670719679326417795 207823607506079518989626693)
  ·
    refine ⟨38966926407389909810555005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 207823607506079518989626693 38966926407389909810555005)
    ·
      refine ⟨14612597402771216178958127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38966926407389909810555005 14612597402771216178958127)
      ·
        refine ⟨21918896104156824268437191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14612597402771216178958127 21918896104156824268437191)
        ·
          refine ⟨32878344156235236402655787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21918896104156824268437191 32878344156235236402655787)
          ·
            refine ⟨49317516234352854603983681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32878344156235236402655787 49317516234352854603983681)
            ·
              refine ⟨36988137175764640952987761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49317516234352854603983681 36988137175764640952987761)
              ·
                refine ⟨27741102881823480714740821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36988137175764640952987761 27741102881823480714740821)
                ·
                  refine ⟨325091049396368914625869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27741102881823480714740821 325091049396368914625869)
                  ·
                    rfl

theorem cell23_5698013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 8].length) (baseStart_5698013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5698013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5698013 prefixEnd_5698013 := by exact prefixLift 5698013
  have htrace : WordTrace (prefixWord ++ tailWord_5698013) baseStart_5698013 baseEnd_5698013 := by
    simpa [prefixWord, tailWord_5698013, baseEnd_5698013] using wordTrace_append hprefix tailTrace_5698013
  have hstable : (prefixWord ++ tailWord_5698013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5698013).length < 2 ^ (prefixWord ++ tailWord_5698013).sum := by decide
  have hdescent : baseEnd_5698013 < baseStart_5698013 := by decide
  rcases family_descends (prefixWord ++ tailWord_5698013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5698017 : List Nat := [1, 2, 3, 1, 2, 2, 4, 3, 1, 4]
def baseStart_5698017 : Nat := 118140960795 + 5698017 * 2 ^ 59
def prefixEnd_5698017 : Nat := 4983230072969 + 3 ^ 40 * 5698017 * 2
def baseEnd_5698017 : Nat := 975273832829979405327601

theorem tailTrace_5698017 : CollatzResearch.WordTrace tailWord_5698017 prefixEnd_5698017 975273832829979405327601 := by
  unfold tailWord_5698017
  simp only [CollatzResearch.WordTrace]
  refine ⟨207823753398065027672772305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138549168932043351781848203 207823753398065027672772305)
  ·
    refine ⟨155867815048548770754579229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207823753398065027672772305 155867815048548770754579229)
    ·
      refine ⟨58450430643205789032967211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155867815048548770754579229 58450430643205789032967211)
      ·
        refine ⟨87675645964808683549450817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58450430643205789032967211 87675645964808683549450817)
        ·
          refine ⟨65756734473606512662088113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87675645964808683549450817 65756734473606512662088113)
          ·
            refine ⟨49317550855204884496566085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65756734473606512662088113 49317550855204884496566085)
            ·
              refine ⟨9247040785350915843106141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49317550855204884496566085 9247040785350915843106141)
              ·
                refine ⟨3467640294506593441164803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9247040785350915843106141 3467640294506593441164803)
                ·
                  refine ⟨5201460441759890161747205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3467640294506593441164803 5201460441759890161747205)
                  ·
                    refine ⟨975273832829979405327601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5201460441759890161747205 975273832829979405327601)
                    ·
                      rfl

theorem cell23_5698017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 3, 1, 4].length) (baseStart_5698017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5698017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5698017 prefixEnd_5698017 := by exact prefixLift 5698017
  have htrace : WordTrace (prefixWord ++ tailWord_5698017) baseStart_5698017 baseEnd_5698017 := by
    simpa [prefixWord, tailWord_5698017, baseEnd_5698017] using wordTrace_append hprefix tailTrace_5698017
  have hstable : (prefixWord ++ tailWord_5698017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5698017).length < 2 ^ (prefixWord ++ tailWord_5698017).sum := by decide
  have hdescent : baseEnd_5698017 < baseStart_5698017 := by decide
  rcases family_descends (prefixWord ++ tailWord_5698017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5698030 : List Nat := [4, 1, 2, 1, 2, 2, 3, 2, 6]
def baseStart_5698030 : Nat := 118140960795 + 5698030 * 2 ^ 59
def prefixEnd_5698030 : Nat := 4983230072969 + 3 ^ 40 * 5698030 * 2
def baseEnd_5698030 : Nat := 325092019304271851680027

theorem tailTrace_5698030 : CollatzResearch.WordTrace tailWord_5698030 prefixEnd_5698030 325092019304271851680027 := by
  unfold tailWord_5698030
  simp only [CollatzResearch.WordTrace]
  refine ⟨25978028443377241361624443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138549485031345287261997029 25978028443377241361624443)
  ·
    refine ⟨38967042665065862042436665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25978028443377241361624443 38967042665065862042436665)
    ·
      refine ⟨29225281998799396531827499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38967042665065862042436665 29225281998799396531827499)
      ·
        refine ⟨43837922998199094797741249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29225281998799396531827499 43837922998199094797741249)
        ·
          refine ⟨32878442248649321098305937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43837922998199094797741249 32878442248649321098305937)
          ·
            refine ⟨24658831686486990823729453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32878442248649321098305937 24658831686486990823729453)
            ·
              refine ⟨9247061882432621558898545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24658831686486990823729453 9247061882432621558898545)
              ·
                refine ⟨6935296411824466169173909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9247061882432621558898545 6935296411824466169173909)
                ·
                  refine ⟨325092019304271851680027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6935296411824466169173909 325092019304271851680027)
                  ·
                    rfl

theorem cell23_5698030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 2, 6].length) (baseStart_5698030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5698030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5698030 prefixEnd_5698030 := by exact prefixLift 5698030
  have htrace : WordTrace (prefixWord ++ tailWord_5698030) baseStart_5698030 baseEnd_5698030 := by
    simpa [prefixWord, tailWord_5698030, baseEnd_5698030] using wordTrace_append hprefix tailTrace_5698030
  have hstable : (prefixWord ++ tailWord_5698030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5698030).length < 2 ^ (prefixWord ++ tailWord_5698030).sum := by decide
  have hdescent : baseEnd_5698030 < baseStart_5698030 := by decide
  rcases family_descends (prefixWord ++ tailWord_5698030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5698060 : List Nat := [2, 2, 1, 2, 4, 1, 1, 4, 1, 5]
def baseStart_5698060 : Nat := 118140960795 + 5698060 * 2 ^ 59
def prefixEnd_5698060 : Nat := 4983230072969 + 3 ^ 40 * 5698060 * 2
def baseEnd_5698060 : Nat := 975281192719360515915035

theorem tailTrace_5698060 : CollatzResearch.WordTrace tailWord_5698060 prefixEnd_5698060 975281192719360515915035 := by
  unfold tailWord_5698060
  simp only [CollatzResearch.WordTrace]
  refine ⟨103912660868454623008293817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138550214491272830677725089 103912660868454623008293817)
  ·
    refine ⟨77934495651340967256220363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103912660868454623008293817 77934495651340967256220363)
    ·
      refine ⟨116901743477011450884330545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77934495651340967256220363 116901743477011450884330545)
      ·
        refine ⟨87676307607758588163247909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116901743477011450884330545 87676307607758588163247909)
        ·
          refine ⟨16439307676454735280608983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87676307607758588163247909 16439307676454735280608983)
          ·
            refine ⟨24658961514682102920913475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16439307676454735280608983 24658961514682102920913475)
            ·
              refine ⟨36988442272023154381370213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24658961514682102920913475 36988442272023154381370213)
              ·
                refine ⟨6935332926004341446506915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36988442272023154381370213 6935332926004341446506915)
                ·
                  refine ⟨10402999389006512169760373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6935332926004341446506915 10402999389006512169760373)
                  ·
                    refine ⟨975281192719360515915035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10402999389006512169760373 975281192719360515915035)
                    ·
                      rfl

theorem cell23_5698060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 4, 1, 5].length) (baseStart_5698060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5698060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5698060 prefixEnd_5698060 := by exact prefixLift 5698060
  have htrace : WordTrace (prefixWord ++ tailWord_5698060) baseStart_5698060 baseEnd_5698060 := by
    simpa [prefixWord, tailWord_5698060, baseEnd_5698060] using wordTrace_append hprefix tailTrace_5698060
  have hstable : (prefixWord ++ tailWord_5698060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5698060).length < 2 ^ (prefixWord ++ tailWord_5698060).sum := by decide
  have hdescent : baseEnd_5698060 < baseStart_5698060 := by decide
  rcases family_descends (prefixWord ++ tailWord_5698060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5698074 : List Nat := [3, 1, 1, 3, 1, 1, 5, 3, 1, 1, 3]
def baseStart_5698074 : Nat := 118140960795 + 5698074 * 2 ^ 59
def prefixEnd_5698074 : Nat := 4983230072969 + 3 ^ 40 * 5698074 * 2
def baseEnd_5698074 : Nat := 2925850766887244492970041

theorem tailTrace_5698074 : CollatzResearch.WordTrace tailWord_5698074 prefixEnd_5698074 2925850766887244492970041 := by
  unfold tailWord_5698074
  simp only [CollatzResearch.WordTrace]
  refine ⟨51956458089714631601899319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138550554905905684271731517 51956458089714631601899319)
  ·
    refine ⟨77934687134571947402848979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51956458089714631601899319 77934687134571947402848979)
    ·
      refine ⟨116902030701857921104273469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77934687134571947402848979 116902030701857921104273469)
      ·
        refine ⟨43838261513196720414102551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116902030701857921104273469 43838261513196720414102551)
        ·
          refine ⟨65757392269795080621153827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43838261513196720414102551 65757392269795080621153827)
          ·
            refine ⟨98636088404692620931730741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65757392269795080621153827 98636088404692620931730741)
            ·
              refine ⟨9247133287939933212349757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 98636088404692620931730741 9247133287939933212349757)
              ·
                refine ⟨3467674982977474954631159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9247133287939933212349757 3467674982977474954631159)
                ·
                  refine ⟨5201512474466212431946739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3467674982977474954631159 5201512474466212431946739)
                  ·
                    refine ⟨7802268711699318647920109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5201512474466212431946739 7802268711699318647920109)
                    ·
                      refine ⟨2925850766887244492970041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7802268711699318647920109 2925850766887244492970041)
                      ·
                        rfl

theorem cell23_5698074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 3, 1, 1, 3].length) (baseStart_5698074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5698074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5698074 prefixEnd_5698074 := by exact prefixLift 5698074
  have htrace : WordTrace (prefixWord ++ tailWord_5698074) baseStart_5698074 baseEnd_5698074 := by
    simpa [prefixWord, tailWord_5698074, baseEnd_5698074] using wordTrace_append hprefix tailTrace_5698074
  have hstable : (prefixWord ++ tailWord_5698074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5698074).length < 2 ^ (prefixWord ++ tailWord_5698074).sum := by decide
  have hdescent : baseEnd_5698074 < baseStart_5698074 := by decide
  rcases family_descends (prefixWord ++ tailWord_5698074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5698103 : List Nat := [1, 1, 3, 1, 2, 3, 4, 8]
def baseStart_5698103 : Nat := 118140960795 + 5698103 * 2 ^ 59
def prefixEnd_5698103 : Nat := 4983230072969 + 3 ^ 40 * 5698103 * 2
def baseEnd_5698103 : Nat := 108365394734304625166941

theorem tailTrace_5698103 : CollatzResearch.WordTrace tailWord_5698103 prefixEnd_5698103 108365394734304625166941 := by
  unfold tailWord_5698103
  simp only [CollatzResearch.WordTrace]
  refine ⟨207826890075753464360402963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138551260050502309573601975 207826890075753464360402963)
  ·
    refine ⟨311740335113630196540604445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207826890075753464360402963 311740335113630196540604445)
    ·
      refine ⟨116902625667611323702726667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 311740335113630196540604445 116902625667611323702726667)
      ·
        refine ⟨175353938501416985554090001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116902625667611323702726667 175353938501416985554090001)
        ·
          refine ⟨131515453876062739165567501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175353938501416985554090001 131515453876062739165567501)
          ·
            refine ⟨49318295203523527187087813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131515453876062739165567501 49318295203523527187087813)
            ·
              refine ⟨9247180350660661347578965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49318295203523527187087813 9247180350660661347578965)
              ·
                refine ⟨108365394734304625166941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9247180350660661347578965 108365394734304625166941)
                ·
                  rfl

theorem cell23_5698103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 8].length) (baseStart_5698103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5698103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5698103 prefixEnd_5698103 := by exact prefixLift 5698103
  have htrace : WordTrace (prefixWord ++ tailWord_5698103) baseStart_5698103 baseEnd_5698103 := by
    simpa [prefixWord, tailWord_5698103, baseEnd_5698103] using wordTrace_append hprefix tailTrace_5698103
  have hstable : (prefixWord ++ tailWord_5698103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5698103).length < 2 ^ (prefixWord ++ tailWord_5698103).sum := by decide
  have hdescent : baseEnd_5698103 < baseStart_5698103 := by decide
  rcases family_descends (prefixWord ++ tailWord_5698103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5698117 : List Nat := [1, 3, 1, 1, 1, 5, 3, 2, 1, 2, 3]
def baseStart_5698117 : Nat := 118140960795 + 5698117 * 2 ^ 59
def prefixEnd_5698117 : Nat := 4983230072969 + 3 ^ 40 * 5698117 * 2
def baseEnd_5698117 : Nat := 2925872846555387824732343

theorem tailTrace_5698117 : CollatzResearch.WordTrace tailWord_5698117 prefixEnd_5698117 2925872846555387824732343 := by
  unfold tailWord_5698117
  simp only [CollatzResearch.WordTrace]
  refine ⟨207827400697702744751412605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138551600465135163167608403 207827400697702744751412605)
  ·
    refine ⟨77935275261638529281779727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207827400697702744751412605 77935275261638529281779727)
    ·
      refine ⟨116902912892457793922669591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77935275261638529281779727 116902912892457793922669591)
      ·
        refine ⟨175354369338686690884004387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116902912892457793922669591 175354369338686690884004387)
        ·
          refine ⟨263031554008030036326006581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175354369338686690884004387 263031554008030036326006581)
          ·
            refine ⟨24659208188252815905563117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 263031554008030036326006581 24659208188252815905563117)
            ·
              refine ⟨9247203070594805964586169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24659208188252815905563117 9247203070594805964586169)
              ·
                refine ⟨6935402302946104473439627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9247203070594805964586169 6935402302946104473439627)
                ·
                  refine ⟨10403103454419156710159441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6935402302946104473439627 10403103454419156710159441)
                  ·
                    refine ⟨7802327590814367532619581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10403103454419156710159441 7802327590814367532619581)
                    ·
                      refine ⟨2925872846555387824732343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7802327590814367532619581 2925872846555387824732343)
                      ·
                        rfl

theorem cell23_5698117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 2, 1, 2, 3].length) (baseStart_5698117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5698117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5698117 prefixEnd_5698117 := by exact prefixLift 5698117
  have htrace : WordTrace (prefixWord ++ tailWord_5698117) baseStart_5698117 baseEnd_5698117 := by
    simpa [prefixWord, tailWord_5698117, baseEnd_5698117] using wordTrace_append hprefix tailTrace_5698117
  have hstable : (prefixWord ++ tailWord_5698117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5698117).length < 2 ^ (prefixWord ++ tailWord_5698117).sum := by decide
  have hdescent : baseEnd_5698117 < baseStart_5698117 := by decide
  rcases family_descends (prefixWord ++ tailWord_5698117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5698143 : List Nat := [1, 1, 2, 3, 1, 1, 1, 4, 2, 2, 5]
def baseStart_5698143 : Nat := 118140960795 + 5698143 * 2 ^ 59
def prefixEnd_5698143 : Nat := 4983230072969 + 3 ^ 40 * 5698143 * 2
def baseEnd_5698143 : Nat := 2925886197052404723007223

theorem tailTrace_5698143 : CollatzResearch.WordTrace tailWord_5698143 prefixEnd_5698143 2925886197052404723007223 := by
  unfold tailWord_5698143
  simp only [CollatzResearch.WordTrace]
  refine ⟨207828348995608551191859083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138552232663739034127906055 207828348995608551191859083)
  ·
    refine ⟨311742523493412826787788625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207828348995608551191859083 311742523493412826787788625)
    ·
      refine ⟨233806892620059620090841469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311742523493412826787788625 233806892620059620090841469)
      ·
        refine ⟨87677584732522357534065551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 233806892620059620090841469 87677584732522357534065551)
        ·
          refine ⟨131516377098783536301098327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87677584732522357534065551 131516377098783536301098327)
          ·
            refine ⟨197274565648175304451647491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131516377098783536301098327 197274565648175304451647491)
            ·
              refine ⟨295911848472262956677471237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197274565648175304451647491 295911848472262956677471237)
              ·
                refine ⟨55483471588549304377025857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 295911848472262956677471237 55483471588549304377025857)
                ·
                  refine ⟨41612603691411978282769393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55483471588549304377025857 41612603691411978282769393)
                  ·
                    refine ⟨31209452768558983712077045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41612603691411978282769393 31209452768558983712077045)
                    ·
                      refine ⟨2925886197052404723007223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31209452768558983712077045 2925886197052404723007223)
                      ·
                        rfl

theorem cell23_5698143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_5698143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5698143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5698143 prefixEnd_5698143 := by exact prefixLift 5698143
  have htrace : WordTrace (prefixWord ++ tailWord_5698143) baseStart_5698143 baseEnd_5698143 := by
    simpa [prefixWord, tailWord_5698143, baseEnd_5698143] using wordTrace_append hprefix tailTrace_5698143
  have hstable : (prefixWord ++ tailWord_5698143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5698143).length < 2 ^ (prefixWord ++ tailWord_5698143).sum := by decide
  have hdescent : baseEnd_5698143 < baseStart_5698143 := by decide
  rcases family_descends (prefixWord ++ tailWord_5698143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5698190 : List Nat := [4, 1, 1, 3, 1, 1, 2, 1, 1, 3, 5]
def baseStart_5698190 : Nat := 118140960795 + 5698190 * 2 ^ 59
def prefixEnd_5698190 : Nat := 4983230072969 + 3 ^ 40 * 5698190 * 2
def baseEnd_5698190 : Nat := 2925910330643166039119507

theorem tailTrace_5698190 : CollatzResearch.WordTrace tailWord_5698190 prefixEnd_5698190 2925910330643166039119507 := by
  unfold tailWord_5698190
  simp only [CollatzResearch.WordTrace]
  refine ⟨25978757903304784777352503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138553375484292185479213349 25978757903304784777352503)
  ·
    refine ⟨38968136854957177166028755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25978757903304784777352503 38968136854957177166028755)
    ·
      refine ⟨58452205282435765749043133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38968136854957177166028755 58452205282435765749043133)
      ·
        refine ⟨21919576980913412155891175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58452205282435765749043133 21919576980913412155891175)
        ·
          refine ⟨32879365471370118233836763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21919576980913412155891175 32879365471370118233836763)
          ·
            refine ⟨49319048207055177350755145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32879365471370118233836763 49319048207055177350755145)
            ·
              refine ⟨36989286155291383013066359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49319048207055177350755145 36989286155291383013066359)
              ·
                refine ⟨55483929232937074519599539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36989286155291383013066359 55483929232937074519599539)
                ·
                  refine ⟨83225893849405611779399309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55483929232937074519599539 83225893849405611779399309)
                  ·
                    refine ⟨31209710193527104417274741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 83225893849405611779399309 31209710193527104417274741)
                    ·
                      refine ⟨2925910330643166039119507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31209710193527104417274741 2925910330643166039119507)
                      ·
                        rfl

theorem cell23_5698190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_5698190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5698190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5698190 prefixEnd_5698190 := by exact prefixLift 5698190
  have htrace : WordTrace (prefixWord ++ tailWord_5698190) baseStart_5698190 baseEnd_5698190 := by
    simpa [prefixWord, tailWord_5698190, baseEnd_5698190] using wordTrace_append hprefix tailTrace_5698190
  have hstable : (prefixWord ++ tailWord_5698190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5698190).length < 2 ^ (prefixWord ++ tailWord_5698190).sum := by decide
  have hdescent : baseEnd_5698190 < baseStart_5698190 := by decide
  rcases family_descends (prefixWord ++ tailWord_5698190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5698200 : List Nat := [2, 1, 2, 4, 1, 1, 1, 1, 4, 2, 4]
def baseStart_5698200 : Nat := 118140960795 + 5698200 * 2 ^ 59
def prefixEnd_5698200 : Nat := 4983230072969 + 3 ^ 40 * 5698200 * 2
def baseEnd_5698200 : Nat := 2925915465449710999994461

theorem tailTrace_5698200 : CollatzResearch.WordTrace tailWord_5698200 prefixEnd_5698200 2925915465449710999994461 := by
  unfold tailWord_5698200
  simp only [CollatzResearch.WordTrace]
  refine ⟨103915213978201024963342027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138553618637601366617789369 103915213978201024963342027)
  ·
    refine ⟨155872820967301537445013041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103915213978201024963342027 155872820967301537445013041)
    ·
      refine ⟨116904615725476153083759781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155872820967301537445013041 116904615725476153083759781)
      ·
        refine ⟨21919615448526778703204959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116904615725476153083759781 21919615448526778703204959)
        ·
          refine ⟨32879423172790168054807439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21919615448526778703204959 32879423172790168054807439)
          ·
            refine ⟨49319134759185252082211159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32879423172790168054807439 49319134759185252082211159)
            ·
              refine ⟨73978702138777878123316739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49319134759185252082211159 73978702138777878123316739)
              ·
                refine ⟨110968053208166817184975109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73978702138777878123316739 110968053208166817184975109)
                ·
                  refine ⟨20806509976531278222182833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 110968053208166817184975109 20806509976531278222182833)
                  ·
                    refine ⟨15604882482398458666637125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20806509976531278222182833 15604882482398458666637125)
                    ·
                      refine ⟨2925915465449710999994461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15604882482398458666637125 2925915465449710999994461)
                      ·
                        rfl

theorem cell23_5698200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_5698200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5698200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5698200 prefixEnd_5698200 := by exact prefixLift 5698200
  have htrace : WordTrace (prefixWord ++ tailWord_5698200) baseStart_5698200 baseEnd_5698200 := by
    simpa [prefixWord, tailWord_5698200, baseEnd_5698200] using wordTrace_append hprefix tailTrace_5698200
  have hstable : (prefixWord ++ tailWord_5698200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5698200).length < 2 ^ (prefixWord ++ tailWord_5698200).sum := by decide
  have hdescent : baseEnd_5698200 < baseStart_5698200 := by decide
  rcases family_descends (prefixWord ++ tailWord_5698200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5698221 : List Nat := [1, 5, 2, 1, 1, 4, 1, 1, 1, 4, 2]
def baseStart_5698221 : Nat := 118140960795 + 5698221 * 2 ^ 59
def prefixEnd_5698221 : Nat := 4983230072969 + 3 ^ 40 * 5698221 * 2
def baseEnd_5698221 : Nat := 2925926248543455417831865

theorem tailTrace_5698221 : CollatzResearch.WordTrace tailWord_5698221 prefixEnd_5698221 2925926248543455417831865 := by
  unfold tailWord_5698221
  simp only [CollatzResearch.WordTrace]
  refine ⟨207831193889325970513198517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138554129259550647008799011 207831193889325970513198517)
  ·
    refine ⟨19484174427124309735612361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 207831193889325970513198517 19484174427124309735612361)
    ·
      refine ⟨14613130820343232301709271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19484174427124309735612361 14613130820343232301709271)
      ·
        refine ⟨21919696230514848452563907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14613130820343232301709271 21919696230514848452563907)
        ·
          refine ⟨32879544345772272678845861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21919696230514848452563907 32879544345772272678845861)
          ·
            refine ⟨6164914564832301127283599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32879544345772272678845861 6164914564832301127283599)
            ·
              refine ⟨9247371847248451690925399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6164914564832301127283599 9247371847248451690925399)
              ·
                refine ⟨13871057770872677536388099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9247371847248451690925399 13871057770872677536388099)
                ·
                  refine ⟨20806586656309016304582149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13871057770872677536388099 20806586656309016304582149)
                  ·
                    refine ⟨3901234998057940557109153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20806586656309016304582149 3901234998057940557109153)
                    ·
                      refine ⟨2925926248543455417831865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3901234998057940557109153 2925926248543455417831865)
                      ·
                        rfl

theorem cell23_5698221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_5698221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5698221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5698221 prefixEnd_5698221 := by exact prefixLift 5698221
  have htrace : WordTrace (prefixWord ++ tailWord_5698221) baseStart_5698221 baseEnd_5698221 := by
    simpa [prefixWord, tailWord_5698221, baseEnd_5698221] using wordTrace_append hprefix tailTrace_5698221
  have hstable : (prefixWord ++ tailWord_5698221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5698221).length < 2 ^ (prefixWord ++ tailWord_5698221).sum := by decide
  have hdescent : baseEnd_5698221 < baseStart_5698221 := by decide
  rcases family_descends (prefixWord ++ tailWord_5698221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5698240 : List Nat := [2, 1, 1, 2, 4, 2, 2, 1, 1, 7]
def baseStart_5698240 : Nat := 118140960795 + 5698240 * 2 ^ 59
def prefixEnd_5698240 : Nat := 4983230072969 + 3 ^ 40 * 5698240 * 2
def baseEnd_5698240 : Nat := 975312001558630281164759

theorem tailTrace_5698240 : CollatzResearch.WordTrace tailWord_5698240 prefixEnd_5698240 975312001558630281164759 := by
  unfold tailWord_5698240
  simp only [CollatzResearch.WordTrace]
  refine ⟨103915943438128568379070087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138554591250838091172093449 103915943438128568379070087)
  ·
    refine ⟨155873915157192852568605131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103915943438128568379070087 155873915157192852568605131)
    ·
      refine ⟨233810872735789278852907697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155873915157192852568605131 233810872735789278852907697)
      ·
        refine ⟨175358154551841959139680773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233810872735789278852907697 175358154551841959139680773)
        ·
          refine ⟨32879653978470367338690145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 175358154551841959139680773 32879653978470367338690145)
          ·
            refine ⟨24659740483852775504017609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32879653978470367338690145 24659740483852775504017609)
            ·
              refine ⟨18494805362889581628013207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24659740483852775504017609 18494805362889581628013207)
              ·
                refine ⟨27742208044334372442019811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18494805362889581628013207 27742208044334372442019811)
                ·
                  refine ⟨41613312066501558663029717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27742208044334372442019811 41613312066501558663029717)
                  ·
                    refine ⟨975312001558630281164759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41613312066501558663029717 975312001558630281164759)
                    ·
                      rfl

theorem cell23_5698240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 1, 7].length) (baseStart_5698240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5698240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5698240 prefixEnd_5698240 := by exact prefixLift 5698240
  have htrace : WordTrace (prefixWord ++ tailWord_5698240) baseStart_5698240 baseEnd_5698240 := by
    simpa [prefixWord, tailWord_5698240, baseEnd_5698240] using wordTrace_append hprefix tailTrace_5698240
  have hstable : (prefixWord ++ tailWord_5698240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5698240).length < 2 ^ (prefixWord ++ tailWord_5698240).sum := by decide
  have hdescent : baseEnd_5698240 < baseStart_5698240 := by decide
  rcases family_descends (prefixWord ++ tailWord_5698240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5698244 : List Nat := [2, 3, 3, 1, 1, 2, 3, 3, 5]
def baseStart_5698244 : Nat := 118140960795 + 5698244 * 2 ^ 59
def prefixEnd_5698244 : Nat := 4983230072969 + 3 ^ 40 * 5698244 * 2
def baseEnd_5698244 : Nat := 325104228733167647538251

theorem tailTrace_5698244 : CollatzResearch.WordTrace tailWord_5698244 prefixEnd_5698244 325104228733167647538251 := by
  unfold tailWord_5698244
  simp only [CollatzResearch.WordTrace]
  refine ⟨103916016384121322720642893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138554688512161763627523857 103916016384121322720642893)
  ·
    refine ⟨38968506144045496020241085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103916016384121322720642893 38968506144045496020241085)
    ·
      refine ⟨14613189804017061007590407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38968506144045496020241085 14613189804017061007590407)
      ·
        refine ⟨21919784706025591511385611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14613189804017061007590407 21919784706025591511385611)
        ·
          refine ⟨32879677059038387267078417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21919784706025591511385611 32879677059038387267078417)
          ·
            refine ⟨24659757794278790450308813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32879677059038387267078417 24659757794278790450308813)
            ·
              refine ⟨9247409172854546418865805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24659757794278790450308813 9247409172854546418865805)
              ·
                refine ⟨3467778439820454907074677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9247409172854546418865805 3467778439820454907074677)
                ·
                  refine ⟨325104228733167647538251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3467778439820454907074677 325104228733167647538251)
                  ·
                    rfl

theorem cell23_5698244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 3, 5].length) (baseStart_5698244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5698244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5698244 prefixEnd_5698244 := by exact prefixLift 5698244
  have htrace : WordTrace (prefixWord ++ tailWord_5698244) baseStart_5698244 baseEnd_5698244 := by
    simpa [prefixWord, tailWord_5698244, baseEnd_5698244] using wordTrace_append hprefix tailTrace_5698244
  have hstable : (prefixWord ++ tailWord_5698244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5698244).length < 2 ^ (prefixWord ++ tailWord_5698244).sum := by decide
  have hdescent : baseEnd_5698244 < baseStart_5698244 := by decide
  rcases family_descends (prefixWord ++ tailWord_5698244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5698261 : List Nat := [1, 3, 2, 5, 2, 1, 1, 1, 7]
def baseStart_5698261 : Nat := 118140960795 + 5698261 * 2 ^ 59
def prefixEnd_5698261 : Nat := 4983230072969 + 3 ^ 40 * 5698261 * 2
def baseEnd_5698261 : Nat := 325105198641070584592409

theorem tailTrace_5698261 : CollatzResearch.WordTrace tailWord_5698261 prefixEnd_5698261 325105198641070584592409 := by
  unfold tailWord_5698261
  simp only [CollatzResearch.WordTrace]
  refine ⟨207832652809181057344654637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138555101872787371563103091 207832652809181057344654637)
  ·
    refine ⟨77937244803442896504245489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207832652809181057344654637 77937244803442896504245489)
    ·
      refine ⟨58452933602582172378184117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77937244803442896504245489 58452933602582172378184117)
      ·
        refine ⟨5479962525242078660454761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58452933602582172378184117 5479962525242078660454761)
        ·
          refine ⟨4109971893931558995341071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5479962525242078660454761 4109971893931558995341071)
          ·
            refine ⟨6164957840897338493011607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4109971893931558995341071 6164957840897338493011607)
            ·
              refine ⟨9247436761346007739517411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6164957840897338493011607 9247436761346007739517411)
              ·
                refine ⟨13871155142019011609276117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9247436761346007739517411 13871155142019011609276117)
                ·
                  refine ⟨325105198641070584592409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13871155142019011609276117 325105198641070584592409)
                  ·
                    rfl

theorem cell23_5698261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 1, 7].length) (baseStart_5698261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5698261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5698261 prefixEnd_5698261 := by exact prefixLift 5698261
  have htrace : WordTrace (prefixWord ++ tailWord_5698261) baseStart_5698261 baseEnd_5698261 := by
    simpa [prefixWord, tailWord_5698261, baseEnd_5698261] using wordTrace_append hprefix tailTrace_5698261
  have hstable : (prefixWord ++ tailWord_5698261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5698261).length < 2 ^ (prefixWord ++ tailWord_5698261).sum := by decide
  have hdescent : baseEnd_5698261 < baseStart_5698261 := by decide
  rcases family_descends (prefixWord ++ tailWord_5698261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5698294 : List Nat := [5, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4]
def baseStart_5698294 : Nat := 118140960795 + 5698294 * 2 ^ 59
def prefixEnd_5698294 : Nat := 4983230072969 + 3 ^ 40 * 5698294 * 2
def baseEnd_5698294 : Nat := 2925963732631233632219029

theorem tailTrace_5698294 : CollatzResearch.WordTrace tailWord_5698294 prefixEnd_5698294 2925963732631233632219029 := by
  unfold tailWord_5698294
  simp only [CollatzResearch.WordTrace]
  refine ⟨12989616026128843998787871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 138555904278707669320403957 12989616026128843998787871)
  ·
    refine ⟨19484424039193265998181807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12989616026128843998787871 19484424039193265998181807)
    ·
      refine ⟨29226636058789898997272711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19484424039193265998181807 29226636058789898997272711)
      ·
        refine ⟨43839954088184848495909067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29226636058789898997272711 43839954088184848495909067)
        ·
          refine ⟨65759931132277272743863601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43839954088184848495909067 65759931132277272743863601)
          ·
            refine ⟨49319948349207954557897701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65759931132277272743863601 49319948349207954557897701)
            ·
              refine ⟨9247490315476491479605819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49319948349207954557897701 9247490315476491479605819)
              ·
                refine ⟨13871235473214737219408729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9247490315476491479605819 13871235473214737219408729)
                ·
                  refine ⟨10403426604911052914556547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13871235473214737219408729 10403426604911052914556547)
                  ·
                    refine ⟨15605139907366579371834821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10403426604911052914556547 15605139907366579371834821)
                    ·
                      refine ⟨2925963732631233632219029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15605139907366579371834821 2925963732631233632219029)
                      ·
                        rfl

theorem cell23_5698294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_5698294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5698294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5698294 prefixEnd_5698294 := by exact prefixLift 5698294
  have htrace : WordTrace (prefixWord ++ tailWord_5698294) baseStart_5698294 baseEnd_5698294 := by
    simpa [prefixWord, tailWord_5698294, baseEnd_5698294] using wordTrace_append hprefix tailTrace_5698294
  have hstable : (prefixWord ++ tailWord_5698294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5698294).length < 2 ^ (prefixWord ++ tailWord_5698294).sum := by decide
  have hdescent : baseEnd_5698294 < baseStart_5698294 := by decide
  rcases family_descends (prefixWord ++ tailWord_5698294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5698321 : List Nat := [1, 2, 2, 1, 1, 3, 6, 2, 1, 4]
def baseStart_5698321 : Nat := 118140960795 + 5698321 * 2 ^ 59
def prefixEnd_5698321 : Nat := 4983230072969 + 3 ^ 40 * 5698321 * 2
def baseEnd_5698321 : Nat := 975325865536301675527135

theorem tailTrace_5698321 : CollatzResearch.WordTrace tailWord_5698321 prefixEnd_5698321 975325865536301675527135 := by
  unfold tailWord_5698321
  simp only [CollatzResearch.WordTrace]
  refine ⟨207834841188963687591838817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138556560792642458394559211 207834841188963687591838817)
  ·
    refine ⟨155876130891722765693879113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207834841188963687591838817 155876130891722765693879113)
    ·
      refine ⟨116907098168792074270409335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155876130891722765693879113 116907098168792074270409335)
      ·
        refine ⟨175360647253188111405614003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116907098168792074270409335 175360647253188111405614003)
        ·
          refine ⟨263040970879782167108421005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175360647253188111405614003 263040970879782167108421005)
          ·
            refine ⟨98640364079918312665657877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 263040970879782167108421005 98640364079918312665657877)
            ·
              refine ⟨4623767066246170906202713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 98640364079918312665657877 4623767066246170906202713)
              ·
                refine ⟨3467825299684628179652035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4623767066246170906202713 3467825299684628179652035)
                ·
                  refine ⟨5201737949526942269478053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3467825299684628179652035 5201737949526942269478053)
                  ·
                    refine ⟨975325865536301675527135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5201737949526942269478053 975325865536301675527135)
                    ·
                      rfl

theorem cell23_5698321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 2, 1, 4].length) (baseStart_5698321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5698321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5698321 prefixEnd_5698321 := by exact prefixLift 5698321
  have htrace : WordTrace (prefixWord ++ tailWord_5698321) baseStart_5698321 baseEnd_5698321 := by
    simpa [prefixWord, tailWord_5698321, baseEnd_5698321] using wordTrace_append hprefix tailTrace_5698321
  have hstable : (prefixWord ++ tailWord_5698321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5698321).length < 2 ^ (prefixWord ++ tailWord_5698321).sum := by decide
  have hdescent : baseEnd_5698321 < baseStart_5698321 := by decide
  rcases family_descends (prefixWord ++ tailWord_5698321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5698354 : List Nat := [3, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2]
def baseStart_5698354 : Nat := 118140960795 + 5698354 * 2 ^ 59
def prefixEnd_5698354 : Nat := 4983230072969 + 3 ^ 40 * 5698354 * 2
def baseEnd_5698354 : Nat := 2925994541470503397468753

theorem tailTrace_5698354 : CollatzResearch.WordTrace tailWord_5698354 prefixEnd_5698354 2925994541470503397468753 := by
  unfold tailWord_5698354
  simp only [CollatzResearch.WordTrace]
  refine ⟨51959011199461033556947529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138557363198562756151860077 51959011199461033556947529)
  ·
    refine ⟨38969258399595775167710647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51959011199461033556947529 38969258399595775167710647)
    ·
      refine ⟨58453887599393662751565971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38969258399595775167710647 58453887599393662751565971)
      ·
        refine ⟨87680831399090494127348957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58453887599393662751565971 87680831399090494127348957)
        ·
          refine ⟨32880311774658935297755859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87680831399090494127348957 32880311774658935297755859)
          ·
            refine ⟨49320467661988402946633789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32880311774658935297755859 49320467661988402946633789)
            ·
              refine ⟨18495175373245651104987671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49320467661988402946633789 18495175373245651104987671)
              ·
                refine ⟨27742763059868476657481507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18495175373245651104987671 27742763059868476657481507)
                ·
                  refine ⟨41614144589802714986222261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27742763059868476657481507 41614144589802714986222261)
                  ·
                    refine ⟨3901326055294004529958337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41614144589802714986222261 3901326055294004529958337)
                    ·
                      refine ⟨2925994541470503397468753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3901326055294004529958337 2925994541470503397468753)
                      ·
                        rfl

theorem cell23_5698354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2].length) (baseStart_5698354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5698354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5698354 prefixEnd_5698354 := by exact prefixLift 5698354
  have htrace : WordTrace (prefixWord ++ tailWord_5698354) baseStart_5698354 baseEnd_5698354 := by
    simpa [prefixWord, tailWord_5698354, baseEnd_5698354] using wordTrace_append hprefix tailTrace_5698354
  have hstable : (prefixWord ++ tailWord_5698354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5698354).length < 2 ^ (prefixWord ++ tailWord_5698354).sum := by decide
  have hdescent : baseEnd_5698354 < baseStart_5698354 := by decide
  rcases family_descends (prefixWord ++ tailWord_5698354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5698387 : List Nat := [1, 1, 1, 2, 1, 1, 3, 3, 5, 2, 3]
def baseStart_5698387 : Nat := 118140960795 + 5698387 * 2 ^ 59
def prefixEnd_5698387 : Nat := 4983230072969 + 3 ^ 40 * 5698387 * 2
def baseEnd_5698387 : Nat := 2926011486332101768356101

theorem tailTrace_5698387 : CollatzResearch.WordTrace tailWord_5698387 prefixEnd_5698387 2926011486332101768356101 := by
  unfold tailWord_5698387
  simp only [CollatzResearch.WordTrace]
  refine ⟨207837248406724580863741415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138558165604483053909160943 207837248406724580863741415)
  ·
    refine ⟨311755872610086871295612123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207837248406724580863741415 311755872610086871295612123)
    ·
      refine ⟨467633808915130306943418185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311755872610086871295612123 467633808915130306943418185)
      ·
        refine ⟨350725356686347730207563639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 467633808915130306943418185 350725356686347730207563639)
        ·
          refine ⟨526088035029521595311345459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350725356686347730207563639 526088035029521595311345459)
          ·
            refine ⟨789132052544282392967018189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 526088035029521595311345459 789132052544282392967018189)
            ·
              refine ⟨295924519704105897362631821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 789132052544282392967018189 295924519704105897362631821)
              ·
                refine ⟨110971694889039711510986933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 295924519704105897362631821 110971694889039711510986933)
                ·
                  refine ⟨10403596395847472954155025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 110971694889039711510986933 10403596395847472954155025)
                  ·
                    refine ⟨7802697296885604715616269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10403596395847472954155025 7802697296885604715616269)
                    ·
                      refine ⟨2926011486332101768356101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7802697296885604715616269 2926011486332101768356101)
                      ·
                        rfl

theorem cell23_5698387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 5, 2, 3].length) (baseStart_5698387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5698387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5698387 prefixEnd_5698387 := by exact prefixLift 5698387
  have htrace : WordTrace (prefixWord ++ tailWord_5698387) baseStart_5698387 baseEnd_5698387 := by
    simpa [prefixWord, tailWord_5698387, baseEnd_5698387] using wordTrace_append hprefix tailTrace_5698387
  have hstable : (prefixWord ++ tailWord_5698387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5698387).length < 2 ^ (prefixWord ++ tailWord_5698387).sum := by decide
  have hdescent : baseEnd_5698387 < baseStart_5698387 := by decide
  rcases family_descends (prefixWord ++ tailWord_5698387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5698394 : List Nat := [3, 1, 1, 2, 1, 6, 1, 1, 1, 6]
def baseStart_5698394 : Nat := 118140960795 + 5698394 * 2 ^ 59
def prefixEnd_5698394 : Nat := 4983230072969 + 3 ^ 40 * 5698394 * 2
def baseEnd_5698394 : Nat := 975338360232227746989523

theorem tailTrace_5698394 : CollatzResearch.WordTrace tailWord_5698394 prefixEnd_5698394 975338360232227746989523 := by
  unfold tailWord_5698394
  simp only [CollatzResearch.WordTrace]
  refine ⟨51959375929424805264811559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138558335811799480706164157 51959375929424805264811559)
  ·
    refine ⟨77939063894137207897217339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51959375929424805264811559 77939063894137207897217339)
    ·
      refine ⟨116908595841205811845826009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77939063894137207897217339 116908595841205811845826009)
      ·
        refine ⟨87681446880904358884369507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116908595841205811845826009 87681446880904358884369507)
        ·
          refine ⟨131522170321356538326554261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87681446880904358884369507 131522170321356538326554261)
          ·
            refine ⟨6165101733813587734057231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 131522170321356538326554261 6165101733813587734057231)
            ·
              refine ⟨9247652600720381601085847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6165101733813587734057231 9247652600720381601085847)
              ·
                refine ⟨13871478901080572401628771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9247652600720381601085847 13871478901080572401628771)
                ·
                  refine ⟨20807218351620858602443157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13871478901080572401628771 20807218351620858602443157)
                  ·
                    refine ⟨975338360232227746989523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20807218351620858602443157 975338360232227746989523)
                    ·
                      rfl

theorem cell23_5698394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 1, 1, 6].length) (baseStart_5698394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5698394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5698394 prefixEnd_5698394 := by exact prefixLift 5698394
  have htrace : WordTrace (prefixWord ++ tailWord_5698394) baseStart_5698394 baseEnd_5698394 := by
    simpa [prefixWord, tailWord_5698394, baseEnd_5698394] using wordTrace_append hprefix tailTrace_5698394
  have hstable : (prefixWord ++ tailWord_5698394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5698394).length < 2 ^ (prefixWord ++ tailWord_5698394).sum := by decide
  have hdescent : baseEnd_5698394 < baseStart_5698394 := by decide
  rcases family_descends (prefixWord ++ tailWord_5698394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5698407 : List Nat := [1, 1, 5, 1, 2, 3, 1, 9]
def baseStart_5698407 : Nat := 118140960795 + 5698407 * 2 ^ 59
def prefixEnd_5698407 : Nat := 4983230072969 + 3 ^ 40 * 5698407 * 2
def baseEnd_5698407 : Nat := 108371176146118210744667

theorem tailTrace_5698407 : CollatzResearch.WordTrace tailWord_5698407 prefixEnd_5698407 108371176146118210744667 := by
  unfold tailWord_5698407
  simp only [CollatzResearch.WordTrace]
  refine ⟨207837977866652124279469475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138558651911101416186312983 207837977866652124279469475)
  ·
    refine ⟨311756966799978186419204213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207837977866652124279469475 311756966799978186419204213)
    ·
      refine ⟨29227215637497954976800395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 311756966799978186419204213 29227215637497954976800395)
      ·
        refine ⟨43840823456246932465200593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29227215637497954976800395 43840823456246932465200593)
        ·
          refine ⟨32880617592185199348900445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43840823456246932465200593 32880617592185199348900445)
          ·
            refine ⟨12330231597069449755837667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32880617592185199348900445 12330231597069449755837667)
            ·
              refine ⟨18495347395604174633756501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12330231597069449755837667 18495347395604174633756501)
              ·
                refine ⟨108371176146118210744667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18495347395604174633756501 108371176146118210744667)
                ·
                  rfl

theorem cell23_5698407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 9].length) (baseStart_5698407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5698407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5698407 prefixEnd_5698407 := by exact prefixLift 5698407
  have htrace : WordTrace (prefixWord ++ tailWord_5698407) baseStart_5698407 baseEnd_5698407 := by
    simpa [prefixWord, tailWord_5698407, baseEnd_5698407] using wordTrace_append hprefix tailTrace_5698407
  have hstable : (prefixWord ++ tailWord_5698407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5698407).length < 2 ^ (prefixWord ++ tailWord_5698407).sum := by decide
  have hdescent : baseEnd_5698407 < baseStart_5698407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5698407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5698421 : List Nat := [1, 3, 4, 1, 1, 2, 2, 3, 1, 2, 3]
def baseStart_5698421 : Nat := 118140960795 + 5698421 * 2 ^ 59
def prefixEnd_5698421 : Nat := 4983230072969 + 3 ^ 40 * 5698421 * 2
def baseEnd_5698421 : Nat := 2926028944674354635330945

theorem tailTrace_5698421 : CollatzResearch.WordTrace tailWord_5698421 prefixEnd_5698421 2926028944674354635330945 := by
  unfold tailWord_5698421
  simp only [CollatzResearch.WordTrace]
  refine ⟨207838488488601404670479117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138558992325734269780319411 207838488488601404670479117)
  ·
    refine ⟨77939433183225526751429669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207838488488601404670479117 77939433183225526751429669)
    ·
      refine ⟨14613643721854786265893063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77939433183225526751429669 14613643721854786265893063)
      ·
        refine ⟨21920465582782179398839595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14613643721854786265893063 21920465582782179398839595)
        ·
          refine ⟨32880698374173269098259393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21920465582782179398839595 32880698374173269098259393)
          ·
            refine ⟨24660523780629951823694545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32880698374173269098259393 24660523780629951823694545)
            ·
              refine ⟨18495392835472463867770909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24660523780629951823694545 18495392835472463867770909)
              ·
                refine ⟨6935772313302173950414091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18495392835472463867770909 6935772313302173950414091)
                ·
                  refine ⟨10403658469953260925621137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6935772313302173950414091 10403658469953260925621137)
                  ·
                    refine ⟨7802743852464945694215853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10403658469953260925621137 7802743852464945694215853)
                    ·
                      refine ⟨2926028944674354635330945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7802743852464945694215853 2926028944674354635330945)
                      ·
                        rfl

theorem cell23_5698421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_5698421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5698421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5698421 prefixEnd_5698421 := by exact prefixLift 5698421
  have htrace : WordTrace (prefixWord ++ tailWord_5698421) baseStart_5698421 baseEnd_5698421 := by
    simpa [prefixWord, tailWord_5698421, baseEnd_5698421] using wordTrace_append hprefix tailTrace_5698421
  have hstable : (prefixWord ++ tailWord_5698421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5698421).length < 2 ^ (prefixWord ++ tailWord_5698421).sum := by decide
  have hdescent : baseEnd_5698421 < baseStart_5698421 := by decide
  rcases family_descends (prefixWord ++ tailWord_5698421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5698435 : List Nat := [1, 1, 1, 3, 4, 1, 5, 2, 1, 2, 2]
def baseStart_5698435 : Nat := 118140960795 + 5698435 * 2 ^ 59
def prefixEnd_5698435 : Nat := 4983230072969 + 3 ^ 40 * 5698435 * 2
def baseEnd_5698435 : Nat := 2926036133403517580555881

theorem tailTrace_5698435 : CollatzResearch.WordTrace tailWord_5698435 prefixEnd_5698435 2926036133403517580555881 := by
  unfold tailWord_5698435
  simp only [CollatzResearch.WordTrace]
  refine ⟨207838999110550685061488759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138559332740367123374325839 207838999110550685061488759)
  ·
    refine ⟨311758498665826027592233139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207838999110550685061488759 311758498665826027592233139)
    ·
      refine ⟨467637747998739041388349709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311758498665826027592233139 467637747998739041388349709)
      ·
        refine ⟨175364155499527140520631141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 467637747998739041388349709 175364155499527140520631141)
        ·
          refine ⟨32880779156161338847618339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 175364155499527140520631141 32880779156161338847618339)
          ·
            refine ⟨49321168734242008271427509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32880779156161338847618339 49321168734242008271427509)
            ·
              refine ⟨4623859568835188275446329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49321168734242008271427509 4623859568835188275446329)
              ·
                refine ⟨3467894676626391206584747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4623859568835188275446329 3467894676626391206584747)
                ·
                  refine ⟨5201842014939586809877121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3467894676626391206584747 5201842014939586809877121)
                  ·
                    refine ⟨3901381511204690107407841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5201842014939586809877121 3901381511204690107407841)
                    ·
                      refine ⟨2926036133403517580555881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3901381511204690107407841 2926036133403517580555881)
                      ·
                        rfl

theorem cell23_5698435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 2, 1, 2, 2].length) (baseStart_5698435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5698435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5698435 prefixEnd_5698435 := by exact prefixLift 5698435
  have htrace : WordTrace (prefixWord ++ tailWord_5698435) baseStart_5698435 baseEnd_5698435 := by
    simpa [prefixWord, tailWord_5698435, baseEnd_5698435] using wordTrace_append hprefix tailTrace_5698435
  have hstable : (prefixWord ++ tailWord_5698435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5698435).length < 2 ^ (prefixWord ++ tailWord_5698435).sum := by decide
  have hdescent : baseEnd_5698435 < baseStart_5698435 := by decide
  rcases family_descends (prefixWord ++ tailWord_5698435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5698461 : List Nat := [1, 4, 2, 1, 2, 1, 3, 1, 3, 3, 2]
def baseStart_5698461 : Nat := 118140960795 + 5698461 * 2 ^ 59
def prefixEnd_5698461 : Nat := 4983230072969 + 3 ^ 40 * 5698461 * 2
def baseEnd_5698461 : Nat := 2926049483900534478830761

theorem tailTrace_5698461 : CollatzResearch.WordTrace tailWord_5698461 prefixEnd_5698461 2926049483900534478830761 := by
  unfold tailWord_5698461
  simp only [CollatzResearch.WordTrace]
  refine ⟨207839947408456491501935237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138559964938970994334623491 207839947408456491501935237)
  ·
    refine ⟨38969990139085592156612857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 207839947408456491501935237 38969990139085592156612857)
    ·
      refine ⟨29227492604314194117459643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38969990139085592156612857 29227492604314194117459643)
      ·
        refine ⟨43841238906471291176189465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29227492604314194117459643 43841238906471291176189465)
        ·
          refine ⟨32880929179853468382142099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43841238906471291176189465 32880929179853468382142099)
          ·
            refine ⟨49321393769780202573213149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32880929179853468382142099 49321393769780202573213149)
            ·
              refine ⟨18495522663667575964954931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49321393769780202573213149 18495522663667575964954931)
              ·
                refine ⟨27743283995501363947432397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18495522663667575964954931 27743283995501363947432397)
                ·
                  refine ⟨10403731498313011480287149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27743283995501363947432397 10403731498313011480287149)
                  ·
                    refine ⟨3901399311867379305107681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10403731498313011480287149 3901399311867379305107681)
                    ·
                      refine ⟨2926049483900534478830761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3901399311867379305107681 2926049483900534478830761)
                      ·
                        rfl

theorem cell23_5698461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 3, 3, 2].length) (baseStart_5698461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5698461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5698461 prefixEnd_5698461 := by exact prefixLift 5698461
  have htrace : WordTrace (prefixWord ++ tailWord_5698461) baseStart_5698461 baseEnd_5698461 := by
    simpa [prefixWord, tailWord_5698461, baseEnd_5698461] using wordTrace_append hprefix tailTrace_5698461
  have hstable : (prefixWord ++ tailWord_5698461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5698461).length < 2 ^ (prefixWord ++ tailWord_5698461).sum := by decide
  have hdescent : baseEnd_5698461 < baseStart_5698461 := by decide
  rcases family_descends (prefixWord ++ tailWord_5698461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5698486 : List Nat := [5, 1, 4, 1, 1, 1, 1, 4, 1, 2, 2]
def baseStart_5698486 : Nat := 118140960795 + 5698486 * 2 ^ 59
def prefixEnd_5698486 : Nat := 4983230072969 + 3 ^ 40 * 5698486 * 2
def baseEnd_5698486 : Nat := 2926062320916896881018147

theorem tailTrace_5698486 : CollatzResearch.WordTrace tailWord_5698486 prefixEnd_5698486 2926062320916896881018147 := by
  unfold tailWord_5698486
  simp only [CollatzResearch.WordTrace]
  refine ⟨12990053702085370048224707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 138560572822243947181063541 12990053702085370048224707)
  ·
    refine ⟨19485080553128055072337061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12990053702085370048224707 19485080553128055072337061)
    ·
      refine ⟨3653452603711510326063199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19485080553128055072337061 3653452603711510326063199)
      ·
        refine ⟨5480178905567265489094799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3653452603711510326063199 5480178905567265489094799)
        ·
          refine ⟨8220268358350898233642199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5480178905567265489094799 8220268358350898233642199)
          ·
            refine ⟨12330402537526347350463299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8220268358350898233642199 12330402537526347350463299)
            ·
              refine ⟨18495603806289521025694949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12330402537526347350463299 18495603806289521025694949)
              ·
                refine ⟨3467925713679285192317803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18495603806289521025694949 3467925713679285192317803)
                ·
                  refine ⟨5201888570518927788476705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3467925713679285192317803 5201888570518927788476705)
                  ·
                    refine ⟨3901416427889195841357529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5201888570518927788476705 3901416427889195841357529)
                    ·
                      refine ⟨2926062320916896881018147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3901416427889195841357529 2926062320916896881018147)
                      ·
                        rfl

theorem cell23_5698486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_5698486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5698486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5698486 prefixEnd_5698486 := by exact prefixLift 5698486
  have htrace : WordTrace (prefixWord ++ tailWord_5698486) baseStart_5698486 baseEnd_5698486 := by
    simpa [prefixWord, tailWord_5698486, baseEnd_5698486] using wordTrace_append hprefix tailTrace_5698486
  have hstable : (prefixWord ++ tailWord_5698486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5698486).length < 2 ^ (prefixWord ++ tailWord_5698486).sum := by decide
  have hdescent : baseEnd_5698486 < baseStart_5698486 := by decide
  rcases family_descends (prefixWord ++ tailWord_5698486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5698494 : List Nat := [4, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3]
def baseStart_5698494 : Nat := 118140960795 + 5698494 * 2 ^ 59
def prefixEnd_5698494 : Nat := 4983230072969 + 3 ^ 40 * 5698494 * 2
def baseEnd_5698494 : Nat := 2926066428762132849718109

theorem tailTrace_5698494 : CollatzResearch.WordTrace tailWord_5698494 prefixEnd_5698494 2926066428762132849718109 := by
  unfold tailWord_5698494
  simp only [CollatzResearch.WordTrace]
  refine ⟨25980143877167117267235817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138560767344891292091924357 25980143877167117267235817)
  ·
    refine ⟨19485107907875337950426863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25980143877167117267235817 19485107907875337950426863)
    ·
      refine ⟨29227661861813006925640295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19485107907875337950426863 29227661861813006925640295)
      ·
        refine ⟨43841492792719510388460443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29227661861813006925640295 43841492792719510388460443)
        ·
          refine ⟨65762239189079265582690665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43841492792719510388460443 65762239189079265582690665)
          ·
            refine ⟨49321679391809449187017999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65762239189079265582690665 49321679391809449187017999)
            ·
              refine ⟨73982519087714173780526999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49321679391809449187017999 73982519087714173780526999)
              ·
                refine ⟨110973778631571260670790499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73982519087714173780526999 110973778631571260670790499)
                ·
                  refine ⟨166460667947356891006185749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110973778631571260670790499 166460667947356891006185749)
                  ·
                    refine ⟨7802843810032354265914957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 166460667947356891006185749 7802843810032354265914957)
                    ·
                      refine ⟨2926066428762132849718109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7802843810032354265914957 2926066428762132849718109)
                      ·
                        rfl

theorem cell23_5698494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_5698494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5698494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5698494 prefixEnd_5698494 := by exact prefixLift 5698494
  have htrace : WordTrace (prefixWord ++ tailWord_5698494) baseStart_5698494 baseEnd_5698494 := by
    simpa [prefixWord, tailWord_5698494, baseEnd_5698494] using wordTrace_append hprefix tailTrace_5698494
  have hstable : (prefixWord ++ tailWord_5698494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5698494).length < 2 ^ (prefixWord ++ tailWord_5698494).sum := by decide
  have hdescent : baseEnd_5698494 < baseStart_5698494 := by decide
  rcases family_descends (prefixWord ++ tailWord_5698494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5698508 : List Nat := [2, 2, 1, 4, 1, 1, 1, 5, 2, 2, 2]
def baseStart_5698508 : Nat := 118140960795 + 5698508 * 2 ^ 59
def prefixEnd_5698508 : Nat := 4983230072969 + 3 ^ 40 * 5698508 * 2
def baseEnd_5698508 : Nat := 2926073617491295794943045

theorem tailTrace_5698508 : CollatzResearch.WordTrace tailWord_5698508 prefixEnd_5698508 2926073617491295794943045 := by
  unfold tailWord_5698508
  simp only [CollatzResearch.WordTrace]
  refine ⟨103920830819643109264448089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138561107759524145685930785 103920830819643109264448089)
  ·
    refine ⟨77940623114732331948336067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103920830819643109264448089 77940623114732331948336067)
    ·
      refine ⟨116910934672098497922504101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77940623114732331948336067 116910934672098497922504101)
      ·
        refine ⟨21920800251018468360469519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116910934672098497922504101 21920800251018468360469519)
        ·
          refine ⟨32881200376527702540704279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21920800251018468360469519 32881200376527702540704279)
          ·
            refine ⟨49321800564791553811056419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32881200376527702540704279 49321800564791553811056419)
            ·
              refine ⟨73982700847187330716584629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49321800564791553811056419 73982700847187330716584629)
              ·
                refine ⟨6935878204423812254679809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73982700847187330716584629 6935878204423812254679809)
                ·
                  refine ⟨5201908653317859191009857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6935878204423812254679809 5201908653317859191009857)
                  ·
                    refine ⟨3901431489988394393257393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5201908653317859191009857 3901431489988394393257393)
                    ·
                      refine ⟨2926073617491295794943045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3901431489988394393257393 2926073617491295794943045)
                      ·
                        rfl

theorem cell23_5698508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_5698508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5698508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5698508 prefixEnd_5698508 := by exact prefixLift 5698508
  have htrace : WordTrace (prefixWord ++ tailWord_5698508) baseStart_5698508 baseEnd_5698508 := by
    simpa [prefixWord, tailWord_5698508, baseEnd_5698508] using wordTrace_append hprefix tailTrace_5698508
  have hstable : (prefixWord ++ tailWord_5698508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5698508).length < 2 ^ (prefixWord ++ tailWord_5698508).sum := by decide
  have hdescent : baseEnd_5698508 < baseStart_5698508 := by decide
  rcases family_descends (prefixWord ++ tailWord_5698508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5698514 : List Nat := [3, 2, 2, 3, 1, 1, 1, 1, 9]
def baseStart_5698514 : Nat := 118140960795 + 5698514 * 2 ^ 59
def prefixEnd_5698514 : Nat := 4983230072969 + 3 ^ 40 * 5698514 * 2
def baseEnd_5698514 : Nat := 325119633152802530163113

theorem tailTrace_5698514 : CollatzResearch.WordTrace tailWord_5698514 prefixEnd_5698514 325119633152802530163113 := by
  unfold tailWord_5698514
  simp only [CollatzResearch.WordTrace]
  refine ⟨51960470119316120388403649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138561253651509654369076397 51960470119316120388403649)
  ·
    refine ⟨38970352589487090291302737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51960470119316120388403649 38970352589487090291302737)
    ·
      refine ⟨29227764442115317718477053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38970352589487090291302737 29227764442115317718477053)
      ·
        refine ⟨10960411665793244144428895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29227764442115317718477053 10960411665793244144428895)
        ·
          refine ⟨16440617498689866216643343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10960411665793244144428895 16440617498689866216643343)
          ·
            refine ⟨24660926248034799324965015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16440617498689866216643343 24660926248034799324965015)
            ·
              refine ⟨36991389372052198987447523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24660926248034799324965015 36991389372052198987447523)
              ·
                refine ⟨55487084058078298481171285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36991389372052198987447523 55487084058078298481171285)
                ·
                  refine ⟨325119633152802530163113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 55487084058078298481171285 325119633152802530163113)
                  ·
                    rfl

theorem cell23_5698514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 9].length) (baseStart_5698514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5698514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5698514 prefixEnd_5698514 := by exact prefixLift 5698514
  have htrace : WordTrace (prefixWord ++ tailWord_5698514) baseStart_5698514 baseEnd_5698514 := by
    simpa [prefixWord, tailWord_5698514, baseEnd_5698514] using wordTrace_append hprefix tailTrace_5698514
  have hstable : (prefixWord ++ tailWord_5698514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5698514).length < 2 ^ (prefixWord ++ tailWord_5698514).sum := by decide
  have hdescent : baseEnd_5698514 < baseStart_5698514 := by decide
  rcases family_descends (prefixWord ++ tailWord_5698514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5698531 : List Nat := [1, 1, 1, 6, 1, 1, 4, 3, 5]
def baseStart_5698531 : Nat := 118140960795 + 5698531 * 2 ^ 59
def prefixEnd_5698531 : Nat := 4983230072969 + 3 ^ 40 * 5698531 * 2
def baseEnd_5698531 : Nat := 325120603060705467217271

theorem tailTrace_5698531 : CollatzResearch.WordTrace tailWord_5698531 prefixEnd_5698531 325120603060705467217271 := by
  unfold tailWord_5698531
  simp only [CollatzResearch.WordTrace]
  refine ⟨207842500518202893456983447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138561667012135262304655631 207842500518202893456983447)
  ·
    refine ⟨311763750777304340185475171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207842500518202893456983447 311763750777304340185475171)
    ·
      refine ⟨467645626165956510278212757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311763750777304340185475171 467645626165956510278212757)
      ·
        refine ⟨21920888726529211419291223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 467645626165956510278212757 21920888726529211419291223)
        ·
          refine ⟨32881333089793817128936835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21920888726529211419291223 32881333089793817128936835)
          ·
            refine ⟨49321999634690725693405253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32881333089793817128936835 49321999634690725693405253)
            ·
              refine ⟨9247874931504511067513485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49321999634690725693405253 9247874931504511067513485)
              ·
                refine ⟨3467953099314191650317557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9247874931504511067513485 3467953099314191650317557)
                ·
                  refine ⟨325120603060705467217271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3467953099314191650317557 325120603060705467217271)
                  ·
                    rfl

theorem cell23_5698531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 3, 5].length) (baseStart_5698531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5698531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5698531 prefixEnd_5698531 := by exact prefixLift 5698531
  have htrace : WordTrace (prefixWord ++ tailWord_5698531) baseStart_5698531 baseEnd_5698531 := by
    simpa [prefixWord, tailWord_5698531, baseEnd_5698531] using wordTrace_append hprefix tailTrace_5698531
  have hstable : (prefixWord ++ tailWord_5698531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5698531).length < 2 ^ (prefixWord ++ tailWord_5698531).sum := by decide
  have hdescent : baseEnd_5698531 < baseStart_5698531 := by decide
  rcases family_descends (prefixWord ++ tailWord_5698531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5698542 : List Nat := [4, 1, 2, 1, 4, 2, 1, 2, 2, 2, 2]
def baseStart_5698542 : Nat := 118140960795 + 5698542 * 2 ^ 59
def prefixEnd_5698542 : Nat := 4983230072969 + 3 ^ 40 * 5698542 * 2
def baseEnd_5698542 : Nat := 2926091075833548661917889

theorem tailTrace_5698542 : CollatzResearch.WordTrace tailWord_5698542 prefixEnd_5698542 2926091075833548661917889 := by
  unfold tailWord_5698542
  simp only [CollatzResearch.WordTrace]
  refine ⟨25980362715145380291954235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138561934480775361557089253 25980362715145380291954235)
  ·
    refine ⟨38970544072718070437931353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25980362715145380291954235 38970544072718070437931353)
    ·
      refine ⟨29227908054538552828448515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38970544072718070437931353 29227908054538552828448515)
      ·
        refine ⟨43841862081807829242672773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29227908054538552828448515 43841862081807829242672773)
        ·
          refine ⟨8220349140338967983001145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43841862081807829242672773 8220349140338967983001145)
          ·
            refine ⟨6165261855254225987250859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8220349140338967983001145 6165261855254225987250859)
            ·
              refine ⟨9247892782881338980876289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6165261855254225987250859 9247892782881338980876289)
              ·
                refine ⟨6935919587161004235657217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9247892782881338980876289 6935919587161004235657217)
                ·
                  refine ⟨5201939690370753176742913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6935919587161004235657217 5201939690370753176742913)
                  ·
                    refine ⟨3901454767778064882557185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5201939690370753176742913 3901454767778064882557185)
                    ·
                      refine ⟨2926091075833548661917889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3901454767778064882557185 2926091075833548661917889)
                      ·
                        rfl

theorem cell23_5698542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 2, 2, 2, 2].length) (baseStart_5698542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5698542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5698542 prefixEnd_5698542 := by exact prefixLift 5698542
  have htrace : WordTrace (prefixWord ++ tailWord_5698542) baseStart_5698542 baseEnd_5698542 := by
    simpa [prefixWord, tailWord_5698542, baseEnd_5698542] using wordTrace_append hprefix tailTrace_5698542
  have hstable : (prefixWord ++ tailWord_5698542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5698542).length < 2 ^ (prefixWord ++ tailWord_5698542).sum := by decide
  have hdescent : baseEnd_5698542 < baseStart_5698542 := by decide
  rcases family_descends (prefixWord ++ tailWord_5698542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5698604 : List Nat := [2, 2, 1, 1, 1, 2, 4, 4, 6]
def baseStart_5698604 : Nat := 118140960795 + 5698604 * 2 ^ 59
def prefixEnd_5698604 : Nat := 4983230072969 + 3 ^ 40 * 5698604 * 2
def baseEnd_5698604 : Nat := 325124767959347491038067

theorem tailTrace_5698604 : CollatzResearch.WordTrace tailWord_5698604 prefixEnd_5698604 325124767959347491038067 := by
  unfold tailWord_5698604
  simp only [CollatzResearch.WordTrace]
  refine ⟨103922581523469213462195433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138563442031292284616260577 103922581523469213462195433)
  ·
    refine ⟨77941936142601910096646575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103922581523469213462195433 77941936142601910096646575)
    ·
      refine ⟨116912904213902865144969863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77941936142601910096646575 116912904213902865144969863)
      ·
        refine ⟨175369356320854297717454795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116912904213902865144969863 175369356320854297717454795)
        ·
          refine ⟨263054034481281446576182193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175369356320854297717454795 263054034481281446576182193)
          ·
            refine ⟨197290525860961084932136645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 263054034481281446576182193 197290525860961084932136645)
            ·
              refine ⟨36991973598930203424775621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 197290525860961084932136645 36991973598930203424775621)
              ·
                refine ⟨6935995049799413142145429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36991973598930203424775621 6935995049799413142145429)
                ·
                  refine ⟨325124767959347491038067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6935995049799413142145429 325124767959347491038067)
                  ·
                    rfl

theorem cell23_5698604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 6].length) (baseStart_5698604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5698604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5698604 prefixEnd_5698604 := by exact prefixLift 5698604
  have htrace : WordTrace (prefixWord ++ tailWord_5698604) baseStart_5698604 baseEnd_5698604 := by
    simpa [prefixWord, tailWord_5698604, baseEnd_5698604] using wordTrace_append hprefix tailTrace_5698604
  have hstable : (prefixWord ++ tailWord_5698604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5698604).length < 2 ^ (prefixWord ++ tailWord_5698604).sum := by decide
  have hdescent : baseEnd_5698604 < baseStart_5698604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5698604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5698621 : List Nat := [1, 4, 1, 3, 1, 3, 1, 3, 6]
def baseStart_5698621 : Nat := 118140960795 + 5698621 * 2 ^ 59
def prefixEnd_5698621 : Nat := 4983230072969 + 3 ^ 40 * 5698621 * 2
def baseEnd_5698621 : Nat := 325125737867250428092225

theorem tailTrace_5698621 : CollatzResearch.WordTrace tailWord_5698621 prefixEnd_5698621 325125737867250428092225 := by
  unfold tailWord_5698621
  simp only [CollatzResearch.WordTrace]
  refine ⟨207845783087876838827759717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138563855391917892551839811 207845783087876838827759717)
  ·
    refine ⟨38971084328976907280204947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 207845783087876838827759717 38971084328976907280204947)
    ·
      refine ⟨58456626493465360920307421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38971084328976907280204947 58456626493465360920307421)
      ·
        refine ⟨21921234935049510345115283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58456626493465360920307421 21921234935049510345115283)
        ·
          refine ⟨32881852402574265517672925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21921234935049510345115283 32881852402574265517672925)
          ·
            refine ⟨12330694650965349569127347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32881852402574265517672925 12330694650965349569127347)
            ·
              refine ⟨18496041976448024353691021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12330694650965349569127347 18496041976448024353691021)
              ·
                refine ⟨6936015741168009132634133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18496041976448024353691021 6936015741168009132634133)
                ·
                  refine ⟨325125737867250428092225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6936015741168009132634133 325125737867250428092225)
                  ·
                    rfl

theorem cell23_5698621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 3, 6].length) (baseStart_5698621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5698621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5698621 prefixEnd_5698621 := by exact prefixLift 5698621
  have htrace : WordTrace (prefixWord ++ tailWord_5698621) baseStart_5698621 baseEnd_5698621 := by
    simpa [prefixWord, tailWord_5698621, baseEnd_5698621] using wordTrace_append hprefix tailTrace_5698621
  have hstable : (prefixWord ++ tailWord_5698621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5698621).length < 2 ^ (prefixWord ++ tailWord_5698621).sum := by decide
  have hdescent : baseEnd_5698621 < baseStart_5698621 := by decide
  rcases family_descends (prefixWord ++ tailWord_5698621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5698641 : List Nat := [1, 2, 2, 1, 3, 1, 2, 3, 1, 5, 2]
def baseStart_5698641 : Nat := 118140960795 + 5698641 * 2 ^ 59
def prefixEnd_5698641 : Nat := 4983230072969 + 3 ^ 40 * 5698641 * 2
def baseEnd_5698641 : Nat := 2926141910418343774579933

theorem tailTrace_5698641 : CollatzResearch.WordTrace tailWord_5698641 prefixEnd_5698641 2926141910418343774579933 := by
  unfold tailWord_5698641
  simp only [CollatzResearch.WordTrace]
  refine ⟨207846512547804382243487777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138564341698536254828991851 207846512547804382243487777)
  ·
    refine ⟨155884884410853286682615833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207846512547804382243487777 155884884410853286682615833)
    ·
      refine ⟨116913663308139965011961875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155884884410853286682615833 116913663308139965011961875)
      ·
        refine ⟨175370494962209947517942813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116913663308139965011961875 175370494962209947517942813)
        ·
          refine ⟨65763935610828730319228555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175370494962209947517942813 65763935610828730319228555)
          ·
            refine ⟨98645903416243095478842833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65763935610828730319228555 98645903416243095478842833)
            ·
              refine ⟨73984427562182321609132125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98645903416243095478842833 73984427562182321609132125)
              ·
                refine ⟨27744160335818370603424547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73984427562182321609132125 27744160335818370603424547)
                ·
                  refine ⟨41616240503727555905136821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27744160335818370603424547 41616240503727555905136821)
                  ·
                    refine ⟨3901522547224458366106577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41616240503727555905136821 3901522547224458366106577)
                    ·
                      refine ⟨2926141910418343774579933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3901522547224458366106577 2926141910418343774579933)
                      ·
                        rfl

theorem cell23_5698641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 5, 2].length) (baseStart_5698641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5698641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5698641 prefixEnd_5698641 := by exact prefixLift 5698641
  have htrace : WordTrace (prefixWord ++ tailWord_5698641) baseStart_5698641 baseEnd_5698641 := by
    simpa [prefixWord, tailWord_5698641, baseEnd_5698641] using wordTrace_append hprefix tailTrace_5698641
  have hstable : (prefixWord ++ tailWord_5698641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5698641).length < 2 ^ (prefixWord ++ tailWord_5698641).sum := by decide
  have hdescent : baseEnd_5698641 < baseStart_5698641 := by decide
  rcases family_descends (prefixWord ++ tailWord_5698641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5698665 : List Nat := [1, 2, 1, 1, 1, 7, 1, 4, 1, 1, 3]
def baseStart_5698665 : Nat := 118140960795 + 5698665 * 2 ^ 59
def prefixEnd_5698665 : Nat := 4983230072969 + 3 ^ 40 * 5698665 * 2
def baseEnd_5698665 : Nat := 2926154233954051680679823

theorem tailTrace_5698665 : CollatzResearch.WordTrace tailWord_5698665 prefixEnd_5698665 2926154233954051680679823 := by
  unfold tailWord_5698665
  simp only [CollatzResearch.WordTrace]
  refine ⟨207847387899717434342361449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138564925266478289561574299 207847387899717434342361449)
  ·
    refine ⟨155885540924788075756771087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207847387899717434342361449 155885540924788075756771087)
    ·
      refine ⟨233828311387182113635156631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155885540924788075756771087 233828311387182113635156631)
      ·
        refine ⟨350742467080773170452734947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233828311387182113635156631 350742467080773170452734947)
        ·
          refine ⟨526113700621159755679102421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350742467080773170452734947 526113700621159755679102421)
          ·
            refine ⟨12330789858308431773728963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 526113700621159755679102421 12330789858308431773728963)
            ·
              refine ⟨18496184787462647660593445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12330789858308431773728963 18496184787462647660593445)
              ·
                refine ⟨3468034647649246436361271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18496184787462647660593445 3468034647649246436361271)
                ·
                  refine ⟨5202051971473869654541907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3468034647649246436361271 5202051971473869654541907)
                  ·
                    refine ⟨7803077957210804481812861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5202051971473869654541907 7803077957210804481812861)
                    ·
                      refine ⟨2926154233954051680679823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7803077957210804481812861 2926154233954051680679823)
                      ·
                        rfl

theorem cell23_5698665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 4, 1, 1, 3].length) (baseStart_5698665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5698665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5698665 prefixEnd_5698665 := by exact prefixLift 5698665
  have htrace : WordTrace (prefixWord ++ tailWord_5698665) baseStart_5698665 baseEnd_5698665 := by
    simpa [prefixWord, tailWord_5698665, baseEnd_5698665] using wordTrace_append hprefix tailTrace_5698665
  have hstable : (prefixWord ++ tailWord_5698665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5698665).length < 2 ^ (prefixWord ++ tailWord_5698665).sum := by decide
  have hdescent : baseEnd_5698665 < baseStart_5698665 := by decide
  rcases family_descends (prefixWord ++ tailWord_5698665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5698686 : List Nat := [4, 2, 4, 1, 2, 1, 1, 1, 2, 2, 3]
def baseStart_5698686 : Nat := 118140960795 + 5698686 * 2 ^ 59
def prefixEnd_5698686 : Nat := 4983230072969 + 3 ^ 40 * 5698686 * 2
def baseEnd_5698686 : Nat := 2926165017047796098517227

theorem tailTrace_5698686 : CollatzResearch.WordTrace tailWord_5698686 prefixEnd_5698686 2926165017047796098517227 := by
  unfold tailWord_5698686
  simp only [CollatzResearch.WordTrace]
  refine ⟨25981019229080169366109489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138565435888427569952583941 25981019229080169366109489)
  ·
    refine ⟨19485764421810127024582117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25981019229080169366109489 19485764421810127024582117)
    ·
      refine ⟨3653580829089398817109147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19485764421810127024582117 3653580829089398817109147)
      ·
        refine ⟨5480371243634098225663721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3653580829089398817109147 5480371243634098225663721)
        ·
          refine ⟨4110278432725573669247791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5480371243634098225663721 4110278432725573669247791)
          ·
            refine ⟨6165417649088360503871687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4110278432725573669247791 6165417649088360503871687)
            ·
              refine ⟨9248126473632540755807531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6165417649088360503871687 9248126473632540755807531)
              ·
                refine ⟨13872189710448811133711297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9248126473632540755807531 13872189710448811133711297)
                ·
                  refine ⟨10404142282836608350283473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13872189710448811133711297 10404142282836608350283473)
                  ·
                    refine ⟨7803106712127456262712605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10404142282836608350283473 7803106712127456262712605)
                    ·
                      refine ⟨2926165017047796098517227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7803106712127456262712605 2926165017047796098517227)
                      ·
                        rfl

theorem cell23_5698686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_5698686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5698686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5698686 prefixEnd_5698686 := by exact prefixLift 5698686
  have htrace : WordTrace (prefixWord ++ tailWord_5698686) baseStart_5698686 baseEnd_5698686 := by
    simpa [prefixWord, tailWord_5698686, baseEnd_5698686] using wordTrace_append hprefix tailTrace_5698686
  have hstable : (prefixWord ++ tailWord_5698686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5698686).length < 2 ^ (prefixWord ++ tailWord_5698686).sum := by decide
  have hdescent : baseEnd_5698686 < baseStart_5698686 := by decide
  rcases family_descends (prefixWord ++ tailWord_5698686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5698688 : List Nat := [2, 1, 1, 2, 1, 3, 3, 1, 5, 2, 2]
def baseStart_5698688 : Nat := 118140960795 + 5698688 * 2 ^ 59
def prefixEnd_5698688 : Nat := 4983230072969 + 3 ^ 40 * 5698688 * 2
def baseEnd_5698688 : Nat := 2926166044009105090692217

theorem tailTrace_5698688 : CollatzResearch.WordTrace tailWord_5698688 prefixEnd_5698688 2926166044009105090692217 := by
  unfold tailWord_5698688
  simp only [CollatzResearch.WordTrace]
  refine ⟨103924113389317054635224359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138565484519089406180299145 103924113389317054635224359)
  ·
    refine ⟨155886170083975581952836539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103924113389317054635224359 155886170083975581952836539)
    ·
      refine ⟨233829255125963372929254809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155886170083975581952836539 233829255125963372929254809)
      ·
        refine ⟨175371941344472529696941107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233829255125963372929254809 175371941344472529696941107)
        ·
          refine ⟨263057912016708794545411661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175371941344472529696941107 263057912016708794545411661)
          ·
            refine ⟨98646717006265797954529373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 263057912016708794545411661 98646717006265797954529373)
            ·
              refine ⟨36992518877349674232948515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98646717006265797954529373 36992518877349674232948515)
              ·
                refine ⟨55488778316024511349422773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36992518877349674232948515 55488778316024511349422773)
                ·
                  refine ⟨5202072967127297939008385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55488778316024511349422773 5202072967127297939008385)
                  ·
                    refine ⟨3901554725345473454256289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5202072967127297939008385 3901554725345473454256289)
                    ·
                      refine ⟨2926166044009105090692217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3901554725345473454256289 2926166044009105090692217)
                      ·
                        rfl

theorem cell23_5698688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 5, 2, 2].length) (baseStart_5698688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5698688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5698688 prefixEnd_5698688 := by exact prefixLift 5698688
  have htrace : WordTrace (prefixWord ++ tailWord_5698688) baseStart_5698688 baseEnd_5698688 := by
    simpa [prefixWord, tailWord_5698688, baseEnd_5698688] using wordTrace_append hprefix tailTrace_5698688
  have hstable : (prefixWord ++ tailWord_5698688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5698688).length < 2 ^ (prefixWord ++ tailWord_5698688).sum := by decide
  have hdescent : baseEnd_5698688 < baseStart_5698688 := by decide
  rcases family_descends (prefixWord ++ tailWord_5698688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5698691 : List Nat := [1, 1, 1, 3, 3, 2, 1, 3, 3, 2, 3]
def baseStart_5698691 : Nat := 118140960795 + 5698691 * 2 ^ 59
def prefixEnd_5698691 : Nat := 4983230072969 + 3 ^ 40 * 5698691 * 2
def baseEnd_5698691 : Nat := 2926167584451068578954703

theorem tailTrace_5698691 : CollatzResearch.WordTrace tailWord_5698691 prefixEnd_5698691 2926167584451068578954703 := by
  unfold tailWord_5698691
  simp only [CollatzResearch.WordTrace]
  refine ⟨207848336197623240782807927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138565557465082160521871951 207848336197623240782807927)
  ·
    refine ⟨311772504296434861174211891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207848336197623240782807927 311772504296434861174211891)
    ·
      refine ⟨467658756444652291761317837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311772504296434861174211891 467658756444652291761317837)
      ·
        refine ⟨175372033666744609410494189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 467658756444652291761317837 175372033666744609410494189)
        ·
          refine ⟨65764512625029228528935321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175372033666744609410494189 65764512625029228528935321)
          ·
            refine ⟨49323384468771921396701491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65764512625029228528935321 49323384468771921396701491)
            ·
              refine ⟨73985076703157882095052237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49323384468771921396701491 73985076703157882095052237)
              ·
                refine ⟨27744403763684205785644589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73985076703157882095052237 27744403763684205785644589)
                ·
                  refine ⟨10404151411381577169616721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27744403763684205785644589 10404151411381577169616721)
                  ·
                    refine ⟨7803113558536182877212541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10404151411381577169616721 7803113558536182877212541)
                    ·
                      refine ⟨2926167584451068578954703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7803113558536182877212541 2926167584451068578954703)
                      ·
                        rfl

theorem cell23_5698691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 3, 2, 3].length) (baseStart_5698691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5698691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5698691 prefixEnd_5698691 := by exact prefixLift 5698691
  have htrace : WordTrace (prefixWord ++ tailWord_5698691) baseStart_5698691 baseEnd_5698691 := by
    simpa [prefixWord, tailWord_5698691, baseEnd_5698691] using wordTrace_append hprefix tailTrace_5698691
  have hstable : (prefixWord ++ tailWord_5698691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5698691).length < 2 ^ (prefixWord ++ tailWord_5698691).sum := by decide
  have hdescent : baseEnd_5698691 < baseStart_5698691 := by decide
  rcases family_descends (prefixWord ++ tailWord_5698691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5698738 : List Nat := [3, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3]
def baseStart_5698738 : Nat := 118140960795 + 5698738 * 2 ^ 59
def prefixEnd_5698738 : Nat := 4983230072969 + 3 ^ 40 * 5698738 * 2
def baseEnd_5698738 : Nat := 2926191718041829895066987

theorem tailTrace_5698738 : CollatzResearch.WordTrace tailWord_5698738 prefixEnd_5698738 2926191718041829895066987 := by
  unfold tailWord_5698738
  simp only [CollatzResearch.WordTrace]
  refine ⟨51962512607113241952442217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138566700285635311873179245 51962512607113241952442217)
  ·
    refine ⟨38971884455334931464331663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51962512607113241952442217 38971884455334931464331663)
    ·
      refine ⟨58457826683002397196497495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38971884455334931464331663 58457826683002397196497495)
      ·
        refine ⟨87686740024503595794746243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58457826683002397196497495 87686740024503595794746243)
        ·
          refine ⟨131530110036755393692119365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87686740024503595794746243 131530110036755393692119365)
          ·
            refine ⟨24661895631891636317272381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 131530110036755393692119365 24661895631891636317272381)
            ·
              refine ⟨9248210861959363618977143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24661895631891636317272381 9248210861959363618977143)
              ·
                refine ⟨13872316292939045428465715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9248210861959363618977143 13872316292939045428465715)
                ·
                  refine ⟨20808474439408568142698573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13872316292939045428465715 20808474439408568142698573)
                  ·
                    refine ⟨7803177914778213053511965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20808474439408568142698573 7803177914778213053511965)
                    ·
                      refine ⟨2926191718041829895066987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7803177914778213053511965 2926191718041829895066987)
                      ·
                        rfl

theorem cell23_5698738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3].length) (baseStart_5698738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5698738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5698738 prefixEnd_5698738 := by exact prefixLift 5698738
  have htrace : WordTrace (prefixWord ++ tailWord_5698738) baseStart_5698738 baseEnd_5698738 := by
    simpa [prefixWord, tailWord_5698738, baseEnd_5698738] using wordTrace_append hprefix tailTrace_5698738
  have hstable : (prefixWord ++ tailWord_5698738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5698738).length < 2 ^ (prefixWord ++ tailWord_5698738).sum := by decide
  have hdescent : baseEnd_5698738 < baseStart_5698738 := by decide
  rcases family_descends (prefixWord ++ tailWord_5698738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5698744 : List Nat := [2, 1, 2, 1, 2, 1, 2, 1, 1, 2, 8]
def baseStart_5698744 : Nat := 118140960795 + 5698744 * 2 ^ 59
def prefixEnd_5698744 : Nat := 4983230072969 + 3 ^ 40 * 5698744 * 2
def baseEnd_5698744 : Nat := 2926194798925756871591959

theorem tailTrace_5698744 : CollatzResearch.WordTrace tailWord_5698744 prefixEnd_5698744 2926194798925756871591959 := by
  unfold tailWord_5698744
  simp only [CollatzResearch.WordTrace]
  refine ⟨103925134633215615417243643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138566846177620820556324857 103925134633215615417243643)
  ·
    refine ⟨155887701949823423125865465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103925134633215615417243643 155887701949823423125865465)
    ·
      refine ⟨116915776462367567344399099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155887701949823423125865465 116915776462367567344399099)
      ·
        refine ⟨175373664693551351016598649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116915776462367567344399099 175373664693551351016598649)
        ·
          refine ⟨131530248520163513262448987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175373664693551351016598649 131530248520163513262448987)
          ·
            refine ⟨197295372780245269893673481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131530248520163513262448987 197295372780245269893673481)
            ·
              refine ⟨147971529585183952420255111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197295372780245269893673481 147971529585183952420255111)
              ·
                refine ⟨221957294377775928630382667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147971529585183952420255111 221957294377775928630382667)
                ·
                  refine ⟨332935941566663892945574001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 221957294377775928630382667 332935941566663892945574001)
                  ·
                    refine ⟨249701956174997919709180501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 332935941566663892945574001 249701956174997919709180501)
                    ·
                      refine ⟨2926194798925756871591959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 249701956174997919709180501 2926194798925756871591959)
                      ·
                        rfl

theorem cell23_5698744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 2, 8].length) (baseStart_5698744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5698744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5698744 prefixEnd_5698744 := by exact prefixLift 5698744
  have htrace : WordTrace (prefixWord ++ tailWord_5698744) baseStart_5698744 baseEnd_5698744 := by
    simpa [prefixWord, tailWord_5698744, baseEnd_5698744] using wordTrace_append hprefix tailTrace_5698744
  have hstable : (prefixWord ++ tailWord_5698744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5698744).length < 2 ^ (prefixWord ++ tailWord_5698744).sum := by decide
  have hdescent : baseEnd_5698744 < baseStart_5698744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5698744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5698756 : List Nat := [2, 3, 3, 1, 3, 2, 1, 3, 1, 2, 2]
def baseStart_5698756 : Nat := 118140960795 + 5698756 * 2 ^ 59
def prefixEnd_5698756 : Nat := 4983230072969 + 3 ^ 40 * 5698756 * 2
def baseEnd_5698756 : Nat := 2926200960693610824641905

theorem tailTrace_5698756 : CollatzResearch.WordTrace tailWord_5698756 prefixEnd_5698756 2926200960693610824641905 := by
  unfold tailWord_5698756
  simp only [CollatzResearch.WordTrace]
  refine ⟨103925353471193878441962061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138567137961591837922616081 103925353471193878441962061)
  ·
    refine ⟨38972007551697704415735773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103925353471193878441962061 38972007551697704415735773)
    ·
      refine ⟨14614502831886639155900915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38972007551697704415735773 14614502831886639155900915)
      ·
        refine ⟨21921754247829958733851373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14614502831886639155900915 21921754247829958733851373)
        ·
          refine ⟨8220657842936234525194265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21921754247829958733851373 8220657842936234525194265)
          ·
            refine ⟨6165493382202175893895699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8220657842936234525194265 6165493382202175893895699)
            ·
              refine ⟨9248240073303263840843549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6165493382202175893895699 9248240073303263840843549)
              ·
                refine ⟨3468090027488723940316331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9248240073303263840843549 3468090027488723940316331)
                ·
                  refine ⟨5202135041233085910474497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3468090027488723940316331 5202135041233085910474497)
                  ·
                    refine ⟨3901601280924814432855873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5202135041233085910474497 3901601280924814432855873)
                    ·
                      refine ⟨2926200960693610824641905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3901601280924814432855873 2926200960693610824641905)
                      ·
                        rfl

theorem cell23_5698756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_5698756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5698756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5698756 prefixEnd_5698756 := by exact prefixLift 5698756
  have htrace : WordTrace (prefixWord ++ tailWord_5698756) baseStart_5698756 baseEnd_5698756 := by
    simpa [prefixWord, tailWord_5698756, baseEnd_5698756] using wordTrace_append hprefix tailTrace_5698756
  have hstable : (prefixWord ++ tailWord_5698756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5698756).length < 2 ^ (prefixWord ++ tailWord_5698756).sum := by decide
  have hdescent : baseEnd_5698756 < baseStart_5698756 := by decide
  rcases family_descends (prefixWord ++ tailWord_5698756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5698789 : List Nat := [1, 3, 1, 4, 3, 2, 2, 1, 2, 1, 3]
def baseStart_5698789 : Nat := 118140960795 + 5698789 * 2 ^ 59
def prefixEnd_5698789 : Nat := 4983230072969 + 3 ^ 40 * 5698789 * 2
def baseEnd_5698789 : Nat := 2926217905555209195529253

theorem tailTrace_5698789 : CollatzResearch.WordTrace tailWord_5698789 prefixEnd_5698789 2926217905555209195529253 := by
  unfold tailWord_5698789
  simp only [CollatzResearch.WordTrace]
  refine ⟨207851910551268203519875421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138567940367512135679916947 207851910551268203519875421)
  ·
    refine ⟨77944466456725576319953283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207851910551268203519875421 77944466456725576319953283)
    ·
      refine ⟨116916699685088364479929925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77944466456725576319953283 116916699685088364479929925)
      ·
        refine ⟨21921881190954068339986861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116916699685088364479929925 21921881190954068339986861)
        ·
          refine ⟨8220705446607775627495073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21921881190954068339986861 8220705446607775627495073)
          ·
            refine ⟨6165529084955831720621305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8220705446607775627495073 6165529084955831720621305)
            ·
              refine ⟨4624146813716873790465979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6165529084955831720621305 4624146813716873790465979)
              ·
                refine ⟨6936220220575310685698969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4624146813716873790465979 6936220220575310685698969)
                ·
                  refine ⟨5202165165431483014274227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6936220220575310685698969 5202165165431483014274227)
                  ·
                    refine ⟨7803247748147224521411341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5202165165431483014274227 7803247748147224521411341)
                    ·
                      refine ⟨2926217905555209195529253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7803247748147224521411341 2926217905555209195529253)
                      ·
                        rfl

theorem cell23_5698789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_5698789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5698789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5698789 prefixEnd_5698789 := by exact prefixLift 5698789
  have htrace : WordTrace (prefixWord ++ tailWord_5698789) baseStart_5698789 baseEnd_5698789 := by
    simpa [prefixWord, tailWord_5698789, baseEnd_5698789] using wordTrace_append hprefix tailTrace_5698789
  have hstable : (prefixWord ++ tailWord_5698789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5698789).length < 2 ^ (prefixWord ++ tailWord_5698789).sum := by decide
  have hdescent : baseEnd_5698789 < baseStart_5698789 := by decide
  rcases family_descends (prefixWord ++ tailWord_5698789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5698799 : List Nat := [1, 1, 2, 1, 8, 1, 1, 2, 1, 3, 2]
def baseStart_5698799 : Nat := 118140960795 + 5698799 * 2 ^ 59
def prefixEnd_5698799 : Nat := 4983230072969 + 3 ^ 40 * 5698799 * 2
def baseEnd_5698799 : Nat := 2926223040361754156404207

theorem tailTrace_5698799 : CollatzResearch.WordTrace tailWord_5698799 prefixEnd_5698799 2926223040361754156404207 := by
  unfold tailWord_5698799
  simp only [CollatzResearch.WordTrace]
  refine ⟨207852275281231975227739451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138568183520821316818492967 207852275281231975227739451)
  ·
    refine ⟨311778412921847962841609177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207852275281231975227739451 311778412921847962841609177)
    ·
      refine ⟨233833809691385972131206883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311778412921847962841609177 233833809691385972131206883)
      ·
        refine ⟨350750714537078958196810325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233833809691385972131206883 350750714537078958196810325)
        ·
          refine ⟨4110359935981394041368871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 350750714537078958196810325 4110359935981394041368871)
          ·
            refine ⟨6165539903972091062053307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4110359935981394041368871 6165539903972091062053307)
            ·
              refine ⟨9248309855958136593079961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6165539903972091062053307 9248309855958136593079961)
              ·
                refine ⟨6936232391968602444809971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9248309855958136593079961 6936232391968602444809971)
                ·
                  refine ⟨10404348587952903667214957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6936232391968602444809971 10404348587952903667214957)
                  ·
                    refine ⟨3901630720482338875205609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10404348587952903667214957 3901630720482338875205609)
                    ·
                      refine ⟨2926223040361754156404207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3901630720482338875205609 2926223040361754156404207)
                      ·
                        rfl

theorem cell23_5698799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 2, 1, 3, 2].length) (baseStart_5698799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5698799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5698799 prefixEnd_5698799 := by exact prefixLift 5698799
  have htrace : WordTrace (prefixWord ++ tailWord_5698799) baseStart_5698799 baseEnd_5698799 := by
    simpa [prefixWord, tailWord_5698799, baseEnd_5698799] using wordTrace_append hprefix tailTrace_5698799
  have hstable : (prefixWord ++ tailWord_5698799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5698799).length < 2 ^ (prefixWord ++ tailWord_5698799).sum := by decide
  have hdescent : baseEnd_5698799 < baseStart_5698799 := by decide
  rcases family_descends (prefixWord ++ tailWord_5698799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5698845 : List Nat := [1, 4, 2, 3, 1, 2, 1, 1, 2, 3, 3]
def baseStart_5698845 : Nat := 118140960795 + 5698845 * 2 ^ 59
def prefixEnd_5698845 : Nat := 4983230072969 + 3 ^ 40 * 5698845 * 2
def baseEnd_5698845 : Nat := 2926246660471860976428995

theorem tailTrace_5698845 : CollatzResearch.WordTrace tailWord_5698845 prefixEnd_5698845 2926246660471860976428995 := by
  unfold tailWord_5698845
  simp only [CollatzResearch.WordTrace]
  refine ⟨207853953039065325083913989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138569302026043550055942659 207853953039065325083913989)
  ·
    refine ⟨38972616194824748453233873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 207853953039065325083913989 38972616194824748453233873)
    ·
      refine ⟨29229462146118561339925405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38972616194824748453233873 29229462146118561339925405)
      ·
        refine ⟨10961048304794460502472027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29229462146118561339925405 10961048304794460502472027)
        ·
          refine ⟨16441572457191690753708041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10961048304794460502472027 16441572457191690753708041)
          ·
            refine ⟨12331179342893768065281031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16441572457191690753708041 12331179342893768065281031)
            ·
              refine ⟨18496769014340652097921547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12331179342893768065281031 18496769014340652097921547)
              ·
                refine ⟨27745153521510978146882321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18496769014340652097921547 27745153521510978146882321)
                ·
                  refine ⟨20808865141133233610161741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27745153521510978146882321 20808865141133233610161741)
                  ·
                    refine ⟨7803324427924962603810653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20808865141133233610161741 7803324427924962603810653)
                    ·
                      refine ⟨2926246660471860976428995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7803324427924962603810653 2926246660471860976428995)
                      ·
                        rfl

theorem cell23_5698845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_5698845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5698845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5698845 prefixEnd_5698845 := by exact prefixLift 5698845
  have htrace : WordTrace (prefixWord ++ tailWord_5698845) baseStart_5698845 baseEnd_5698845 := by
    simpa [prefixWord, tailWord_5698845, baseEnd_5698845] using wordTrace_append hprefix tailTrace_5698845
  have hstable : (prefixWord ++ tailWord_5698845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5698845).length < 2 ^ (prefixWord ++ tailWord_5698845).sum := by decide
  have hdescent : baseEnd_5698845 < baseStart_5698845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5698845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5698865 : List Nat := [1, 2, 2, 3, 3, 3, 1, 1, 2, 5]
def baseStart_5698865 : Nat := 118140960795 + 5698865 * 2 ^ 59
def prefixEnd_5698865 : Nat := 4983230072969 + 3 ^ 40 * 5698865 * 2
def baseEnd_5698865 : Nat := 975418976694983632726301

theorem tailTrace_5698865 : CollatzResearch.WordTrace tailWord_5698865 prefixEnd_5698865 975418976694983632726301 := by
  unfold tailWord_5698865
  simp only [CollatzResearch.WordTrace]
  refine ⟨207854682498992868499642049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138569788332661912333094699 207854682498992868499642049)
  ·
    refine ⟨155891011874244651374731537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207854682498992868499642049 155891011874244651374731537)
    ·
      refine ⟨116918258905683488531048653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155891011874244651374731537 116918258905683488531048653)
      ·
        refine ⟨43844347089631308199143245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116918258905683488531048653 43844347089631308199143245)
        ·
          refine ⟨16441630158611740574678717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43844347089631308199143245 16441630158611740574678717)
          ·
            refine ⟨6165611309479402715504519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16441630158611740574678717 6165611309479402715504519)
            ·
              refine ⟨9248416964219104073256779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6165611309479402715504519 9248416964219104073256779)
              ·
                refine ⟨13872625446328656109885169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9248416964219104073256779 13872625446328656109885169)
                ·
                  refine ⟨10404469084746492082413877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13872625446328656109885169 10404469084746492082413877)
                  ·
                    refine ⟨975418976694983632726301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10404469084746492082413877 975418976694983632726301)
                    ·
                      rfl

theorem cell23_5698865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 1, 2, 5].length) (baseStart_5698865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5698865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5698865 prefixEnd_5698865 := by exact prefixLift 5698865
  have htrace : WordTrace (prefixWord ++ tailWord_5698865) baseStart_5698865 baseEnd_5698865 := by
    simpa [prefixWord, tailWord_5698865, baseEnd_5698865] using wordTrace_append hprefix tailTrace_5698865
  have hstable : (prefixWord ++ tailWord_5698865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5698865).length < 2 ^ (prefixWord ++ tailWord_5698865).sum := by decide
  have hdescent : baseEnd_5698865 < baseStart_5698865 := by decide
  rcases family_descends (prefixWord ++ tailWord_5698865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5698888 : List Nat := [2, 1, 3, 1, 1, 2, 1, 3, 4, 2, 3]
def baseStart_5698888 : Nat := 118140960795 + 5698888 * 2 ^ 59
def prefixEnd_5698888 : Nat := 4983230072969 + 3 ^ 40 * 5698888 * 2
def baseEnd_5698888 : Nat := 2926268740140004308191297

theorem tailTrace_5698888 : CollatzResearch.WordTrace tailWord_5698888 prefixEnd_5698888 2926268740140004308191297 := by
  unfold tailWord_5698888
  simp only [CollatzResearch.WordTrace]
  refine ⟨103927760688954771713864659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138570347585273028951819545 103927760688954771713864659)
  ·
    refine ⟨155891641033432157570796989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103927760688954771713864659 155891641033432157570796989)
    ·
      refine ⟨58459365387537059089048871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155891641033432157570796989 58459365387537059089048871)
      ·
        refine ⟨87689048081305588633573307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58459365387537059089048871 87689048081305588633573307)
        ·
          refine ⟨131533572121958382950359961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87689048081305588633573307 131533572121958382950359961)
          ·
            refine ⟨98650179091468787212769971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131533572121958382950359961 98650179091468787212769971)
            ·
              refine ⟨147975268637203180819154957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98650179091468787212769971 147975268637203180819154957)
              ·
                refine ⟨55490725738951192807183109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 147975268637203180819154957 55490725738951192807183109)
                ·
                  refine ⟨10404511076053348651346833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55490725738951192807183109 10404511076053348651346833)
                  ·
                    refine ⟨7803383307040011488510125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10404511076053348651346833 7803383307040011488510125)
                    ·
                      refine ⟨2926268740140004308191297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7803383307040011488510125 2926268740140004308191297)
                      ·
                        rfl

theorem cell23_5698888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 4, 2, 3].length) (baseStart_5698888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5698888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5698888 prefixEnd_5698888 := by exact prefixLift 5698888
  have htrace : WordTrace (prefixWord ++ tailWord_5698888) baseStart_5698888 baseEnd_5698888 := by
    simpa [prefixWord, tailWord_5698888, baseEnd_5698888] using wordTrace_append hprefix tailTrace_5698888
  have hstable : (prefixWord ++ tailWord_5698888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5698888).length < 2 ^ (prefixWord ++ tailWord_5698888).sum := by decide
  have hdescent : baseEnd_5698888 < baseStart_5698888 := by decide
  rcases family_descends (prefixWord ++ tailWord_5698888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5698911 : List Nat := [1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 6]
def baseStart_5698911 : Nat := 118140960795 + 5698911 * 2 ^ 59
def prefixEnd_5698911 : Nat := 4983230072969 + 3 ^ 40 * 5698911 * 2
def baseEnd_5698911 : Nat := 2926280550195057718203691

theorem tailTrace_5698911 : CollatzResearch.WordTrace tailWord_5698911 prefixEnd_5698911 2926280550195057718203691 := by
  unfold tailWord_5698911
  simp only [CollatzResearch.WordTrace]
  refine ⟨207856360256826218355816587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138570906837884145570544391 207856360256826218355816587)
  ·
    refine ⟨311784540385239327533724881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207856360256826218355816587 311784540385239327533724881)
    ·
      refine ⟨233838405288929495650293661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311784540385239327533724881 233838405288929495650293661)
      ·
        refine ⟨87689401983348560868860123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 233838405288929495650293661 87689401983348560868860123)
        ·
          refine ⟨131534102975022841303290185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87689401983348560868860123 131534102975022841303290185)
          ·
            refine ⟨98650577231267130977467639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131534102975022841303290185 98650577231267130977467639)
            ·
              refine ⟨147975865846900696466201459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98650577231267130977467639 147975865846900696466201459)
              ·
                refine ⟨221963798770351044699302189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147975865846900696466201459 221963798770351044699302189)
                ·
                  refine ⟨83236424538881641762238321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 221963798770351044699302189 83236424538881641762238321)
                  ·
                    refine ⟨62427318404161231321678741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 83236424538881641762238321 62427318404161231321678741)
                    ·
                      refine ⟨2926280550195057718203691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62427318404161231321678741 2926280550195057718203691)
                      ·
                        rfl

theorem cell23_5698911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_5698911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5698911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5698911 prefixEnd_5698911 := by exact prefixLift 5698911
  have htrace : WordTrace (prefixWord ++ tailWord_5698911) baseStart_5698911 baseEnd_5698911 := by
    simpa [prefixWord, tailWord_5698911, baseEnd_5698911] using wordTrace_append hprefix tailTrace_5698911
  have hstable : (prefixWord ++ tailWord_5698911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5698911).length < 2 ^ (prefixWord ++ tailWord_5698911).sum := by decide
  have hdescent : baseEnd_5698911 < baseStart_5698911 := by decide
  rcases family_descends (prefixWord ++ tailWord_5698911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5698931 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 1, 6, 5]
def baseStart_5698931 : Nat := 118140960795 + 5698931 * 2 ^ 59
def prefixEnd_5698931 : Nat := 4983230072969 + 3 ^ 40 * 5698931 * 2
def baseEnd_5698931 : Nat := 2926290819808147639953599

theorem tailTrace_5698931 : CollatzResearch.WordTrace tailWord_5698931 prefixEnd_5698931 2926290819808147639953599 := by
  unfold tailWord_5698931
  simp only [CollatzResearch.WordTrace]
  refine ⟨207857089716753761771544647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138571393144502507847696431 207857089716753761771544647)
  ·
    refine ⟨311785634575130642657316971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207857089716753761771544647 311785634575130642657316971)
    ·
      refine ⟨467678451862695963985975457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311785634575130642657316971 467678451862695963985975457)
      ·
        refine ⟨350758838897021972989481593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 467678451862695963985975457 350758838897021972989481593)
        ·
          refine ⟨263069129172766479742111195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 350758838897021972989481593 263069129172766479742111195)
          ·
            refine ⟨394603693759149719613166793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263069129172766479742111195 394603693759149719613166793)
            ·
              refine ⟨295952770319362289709875095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 394603693759149719613166793 295952770319362289709875095)
              ·
                refine ⟨443929155479043434564812643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 295952770319362289709875095 443929155479043434564812643)
                ·
                  refine ⟨665893733218565151847218965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 443929155479043434564812643 665893733218565151847218965)
                  ·
                    refine ⟨31213768744620241492838389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 665893733218565151847218965 31213768744620241492838389)
                    ·
                      refine ⟨2926290819808147639953599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31213768744620241492838389 2926290819808147639953599)
                      ·
                        rfl

theorem cell23_5698931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6, 5].length) (baseStart_5698931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5698931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5698931 prefixEnd_5698931 := by exact prefixLift 5698931
  have htrace : WordTrace (prefixWord ++ tailWord_5698931) baseStart_5698931 baseEnd_5698931 := by
    simpa [prefixWord, tailWord_5698931, baseEnd_5698931] using wordTrace_append hprefix tailTrace_5698931
  have hstable : (prefixWord ++ tailWord_5698931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5698931).length < 2 ^ (prefixWord ++ tailWord_5698931).sum := by decide
  have hdescent : baseEnd_5698931 < baseStart_5698931 := by decide
  rcases family_descends (prefixWord ++ tailWord_5698931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5698952 : List Nat := [2, 1, 3, 3, 1, 2, 3, 1, 3, 1, 3]
def baseStart_5698952 : Nat := 118140960795 + 5698952 * 2 ^ 59
def prefixEnd_5698952 : Nat := 4983230072969 + 3 ^ 40 * 5698952 * 2
def baseEnd_5698952 : Nat := 2926301602901892057791003

theorem tailTrace_5698952 : CollatzResearch.WordTrace tailWord_5698952 prefixEnd_5698952 2926301602901892057791003 := by
  unfold tailWord_5698952
  simp only [CollatzResearch.WordTrace]
  refine ⟨103928927824838841179029555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138571903766451788238706073 103928927824838841179029555)
  ·
    refine ⟨155893391737258261768544333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103928927824838841179029555 155893391737258261768544333)
    ·
      refine ⟨58460021901471848163204125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155893391737258261768544333 58460021901471848163204125)
      ·
        refine ⟨21922508213051943061201547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58460021901471848163204125 21922508213051943061201547)
        ·
          refine ⟨32883762319577914591802321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21922508213051943061201547 32883762319577914591802321)
          ·
            refine ⟨24662821739683435943851741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32883762319577914591802321 24662821739683435943851741)
            ·
              refine ⟨9248558152381288478944403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24662821739683435943851741 9248558152381288478944403)
              ·
                refine ⟨13872837228571932718416605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9248558152381288478944403 13872837228571932718416605)
                ·
                  refine ⟨5202313960714474769406227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13872837228571932718416605 5202313960714474769406227)
                  ·
                    refine ⟨7803470941071712154109341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5202313960714474769406227 7803470941071712154109341)
                    ·
                      refine ⟨2926301602901892057791003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7803470941071712154109341 2926301602901892057791003)
                      ·
                        rfl

theorem cell23_5698952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_5698952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5698952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5698952 prefixEnd_5698952 := by exact prefixLift 5698952
  have htrace : WordTrace (prefixWord ++ tailWord_5698952) baseStart_5698952 baseEnd_5698952 := by
    simpa [prefixWord, tailWord_5698952, baseEnd_5698952] using wordTrace_append hprefix tailTrace_5698952
  have hstable : (prefixWord ++ tailWord_5698952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5698952).length < 2 ^ (prefixWord ++ tailWord_5698952).sum := by decide
  have hdescent : baseEnd_5698952 < baseStart_5698952 := by decide
  rcases family_descends (prefixWord ++ tailWord_5698952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5698972 : List Nat := [2, 2, 3, 4, 1, 1, 1, 1, 3, 5]
def baseStart_5698972 : Nat := 118140960795 + 5698972 * 2 ^ 59
def prefixEnd_5698972 : Nat := 4983230072969 + 3 ^ 40 * 5698972 * 2
def baseEnd_5698972 : Nat := 975437290838327326513637

theorem tailTrace_5698972 : CollatzResearch.WordTrace tailWord_5698972 prefixEnd_5698972 975437290838327326513637 := by
  unfold tailWord_5698972
  simp only [CollatzResearch.WordTrace]
  refine ⟨103929292554802612886893585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138572390073070150515858113 103929292554802612886893585)
  ·
    refine ⟨77946969416101959665170189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103929292554802612886893585 77946969416101959665170189)
    ·
      refine ⟨29230113531038234874438821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77946969416101959665170189 29230113531038234874438821)
      ·
        refine ⟨5480646287069669038957279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29230113531038234874438821 5480646287069669038957279)
        ·
          refine ⟨8220969430604503558435919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5480646287069669038957279 8220969430604503558435919)
          ·
            refine ⟨12331454145906755337653879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8220969430604503558435919 12331454145906755337653879)
            ·
              refine ⟨18497181218860133006480819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12331454145906755337653879 18497181218860133006480819)
              ·
                refine ⟨27745771828290199509721229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18497181218860133006480819 27745771828290199509721229)
                ·
                  refine ⟨10404664435608824816145461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27745771828290199509721229 10404664435608824816145461)
                  ·
                    refine ⟨975437290838327326513637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10404664435608824816145461 975437290838327326513637)
                    ·
                      rfl

theorem cell23_5698972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_5698972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5698972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5698972 prefixEnd_5698972 := by exact prefixLift 5698972
  have htrace : WordTrace (prefixWord ++ tailWord_5698972) baseStart_5698972 baseEnd_5698972 := by
    simpa [prefixWord, tailWord_5698972, baseEnd_5698972] using wordTrace_append hprefix tailTrace_5698972
  have hstable : (prefixWord ++ tailWord_5698972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5698972).length < 2 ^ (prefixWord ++ tailWord_5698972).sum := by decide
  have hdescent : baseEnd_5698972 < baseStart_5698972 := by decide
  rcases family_descends (prefixWord ++ tailWord_5698972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5698975 : List Nat := [1, 1, 2, 5, 1, 3, 1, 1, 3, 1, 4]
def baseStart_5698975 : Nat := 118140960795 + 5698975 * 2 ^ 59
def prefixEnd_5698975 : Nat := 4983230072969 + 3 ^ 40 * 5698975 * 2
def baseEnd_5698975 : Nat := 2926313412956945467803397

theorem tailTrace_5698975 : CollatzResearch.WordTrace tailWord_5698975 prefixEnd_5698975 2926313412956945467803397 := by
  unfold tailWord_5698975
  simp only [CollatzResearch.WordTrace]
  refine ⟨207858694528594357286146379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138572463019062904857430919 207858694528594357286146379)
  ·
    refine ⟨311788041792891535929219569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207858694528594357286146379 311788041792891535929219569)
    ·
      refine ⟨233841031344668651946914677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311788041792891535929219569 233841031344668651946914677)
      ·
        refine ⟨21922596688562686120023251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 233841031344668651946914677 21922596688562686120023251)
        ·
          refine ⟨32883895032844029180034877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21922596688562686120023251 32883895032844029180034877)
          ·
            refine ⟨12331460637316510942513079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32883895032844029180034877 12331460637316510942513079)
            ·
              refine ⟨18497190955974766413769619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12331460637316510942513079 18497190955974766413769619)
              ·
                refine ⟨27745786433962149620654429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18497190955974766413769619 27745786433962149620654429)
                ·
                  refine ⟨10404669912735806107745411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27745786433962149620654429 10404669912735806107745411)
                  ·
                    refine ⟨15607004869103709161618117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10404669912735806107745411 15607004869103709161618117)
                    ·
                      refine ⟨2926313412956945467803397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15607004869103709161618117 2926313412956945467803397)
                      ·
                        rfl

theorem cell23_5698975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_5698975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5698975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5698975 prefixEnd_5698975 := by exact prefixLift 5698975
  have htrace : WordTrace (prefixWord ++ tailWord_5698975) baseStart_5698975 baseEnd_5698975 := by
    simpa [prefixWord, tailWord_5698975, baseEnd_5698975] using wordTrace_append hprefix tailTrace_5698975
  have hstable : (prefixWord ++ tailWord_5698975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5698975).length < 2 ^ (prefixWord ++ tailWord_5698975).sum := by decide
  have hdescent : baseEnd_5698975 < baseStart_5698975 := by decide
  rcases family_descends (prefixWord ++ tailWord_5698975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5698988 : List Nat := [2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 4]
def baseStart_5698988 : Nat := 118140960795 + 5698988 * 2 ^ 59
def prefixEnd_5698988 : Nat := 4983230072969 + 3 ^ 40 * 5698988 * 2
def baseEnd_5698988 : Nat := 2926320088205453916940837

theorem tailTrace_5698988 : CollatzResearch.WordTrace tailWord_5698988 prefixEnd_5698988 2926320088205453916940837 := by
  unfold tailWord_5698988
  simp only [CollatzResearch.WordTrace]
  refine ⟨103929584338773630253184809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138572779118364840337579745 103929584338773630253184809)
  ·
    refine ⟨77947188254080222689888607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103929584338773630253184809 77947188254080222689888607)
    ·
      refine ⟨116920782381120334034832911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77947188254080222689888607 116920782381120334034832911)
      ·
        refine ⟨175381173571680501052249367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116920782381120334034832911 175381173571680501052249367)
        ·
          refine ⟨263071760357520751578374051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175381173571680501052249367 263071760357520751578374051)
          ·
            refine ⟨394607640536281127367561077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263071760357520751578374051 394607640536281127367561077)
            ·
              refine ⟨36994466300276355690708851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 394607640536281127367561077 36994466300276355690708851)
              ·
                refine ⟨55491699450414533536063277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36994466300276355690708851 55491699450414533536063277)
                ·
                  refine ⟨20809387293905450076023729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55491699450414533536063277 20809387293905450076023729)
                  ·
                    refine ⟨15607040470429087557017797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20809387293905450076023729 15607040470429087557017797)
                    ·
                      refine ⟨2926320088205453916940837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15607040470429087557017797 2926320088205453916940837)
                      ·
                        rfl

theorem cell23_5698988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 4].length) (baseStart_5698988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5698988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5698988 prefixEnd_5698988 := by exact prefixLift 5698988
  have htrace : WordTrace (prefixWord ++ tailWord_5698988) baseStart_5698988 baseEnd_5698988 := by
    simpa [prefixWord, tailWord_5698988, baseEnd_5698988] using wordTrace_append hprefix tailTrace_5698988
  have hstable : (prefixWord ++ tailWord_5698988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5698988).length < 2 ^ (prefixWord ++ tailWord_5698988).sum := by decide
  have hdescent : baseEnd_5698988 < baseStart_5698988 := by decide
  rcases family_descends (prefixWord ++ tailWord_5698988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5698989 : List Nat := [1, 5, 2, 2, 1, 2, 3, 1, 1, 5]
def baseStart_5698989 : Nat := 118140960795 + 5698989 * 2 ^ 59
def prefixEnd_5698989 : Nat := 4983230072969 + 3 ^ 40 * 5698989 * 2
def baseEnd_5698989 : Nat := 975440200562036137676111

theorem tailTrace_5698989 : CollatzResearch.WordTrace tailWord_5698989 prefixEnd_5698989 975440200562036137676111 := by
  unfold tailWord_5698989
  simp only [CollatzResearch.WordTrace]
  refine ⟨207859205150543637677156021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138572803433695758451437347 207859205150543637677156021)
  ·
    refine ⟨19486800482863466032233377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 207859205150543637677156021 19486800482863466032233377)
    ·
      refine ⟨14615100362147599524175033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19486800482863466032233377 14615100362147599524175033)
      ·
        refine ⟨10961325271610699643131275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14615100362147599524175033 10961325271610699643131275)
        ·
          refine ⟨16441987907416049464696913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10961325271610699643131275 16441987907416049464696913)
          ·
            refine ⟨12331490930562037098522685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16441987907416049464696913 12331490930562037098522685)
            ·
              refine ⟨4624309098960763911946007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12331490930562037098522685 4624309098960763911946007)
              ·
                refine ⟨6936463648441145867919011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4624309098960763911946007 6936463648441145867919011)
                ·
                  refine ⟨10404695472661718801878517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6936463648441145867919011 10404695472661718801878517)
                  ·
                    refine ⟨975440200562036137676111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10404695472661718801878517 975440200562036137676111)
                    ·
                      rfl

theorem cell23_5698989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_5698989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5698989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5698989 prefixEnd_5698989 := by exact prefixLift 5698989
  have htrace : WordTrace (prefixWord ++ tailWord_5698989) baseStart_5698989 baseEnd_5698989 := by
    simpa [prefixWord, tailWord_5698989, baseEnd_5698989] using wordTrace_append hprefix tailTrace_5698989
  have hstable : (prefixWord ++ tailWord_5698989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5698989).length < 2 ^ (prefixWord ++ tailWord_5698989).sum := by decide
  have hdescent : baseEnd_5698989 < baseStart_5698989 := by decide
  rcases family_descends (prefixWord ++ tailWord_5698989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5698995 : List Nat := [1, 1, 1, 2, 3, 1, 1, 7, 1, 2, 3]
def baseStart_5698995 : Nat := 118140960795 + 5698995 * 2 ^ 59
def prefixEnd_5698995 : Nat := 4983230072969 + 3 ^ 40 * 5698995 * 2
def baseEnd_5698995 : Nat := 2926323682570035389553305

theorem tailTrace_5698995 : CollatzResearch.WordTrace tailWord_5698995 prefixEnd_5698995 2926323682570035389553305 := by
  unfold tailWord_5698995
  simp only [CollatzResearch.WordTrace]
  refine ⟨207859423988521900701874439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138572949325681267134582959 207859423988521900701874439)
  ·
    refine ⟨311789135982782851052811659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207859423988521900701874439 311789135982782851052811659)
    ·
      refine ⟨467683703974174276579217489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311789135982782851052811659 467683703974174276579217489)
      ·
        refine ⟨350762777980630707434413117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 467683703974174276579217489 350762777980630707434413117)
        ·
          refine ⟨131536041742736515287904919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 350762777980630707434413117 131536041742736515287904919)
          ·
            refine ⟨197304062614104772931857379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131536041742736515287904919 197304062614104772931857379)
            ·
              refine ⟨295956093921157159397786069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197304062614104772931857379 295956093921157159397786069)
              ·
                refine ⟨6936470951277120923385611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 295956093921157159397786069 6936470951277120923385611)
                ·
                  refine ⟨10404706426915681385078417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6936470951277120923385611 10404706426915681385078417)
                  ·
                    refine ⟨7803529820186761038808813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10404706426915681385078417 7803529820186761038808813)
                    ·
                      refine ⟨2926323682570035389553305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7803529820186761038808813 2926323682570035389553305)
                      ·
                        rfl

theorem cell23_5698995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 7, 1, 2, 3].length) (baseStart_5698995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5698995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5698995 prefixEnd_5698995 := by exact prefixLift 5698995
  have htrace : WordTrace (prefixWord ++ tailWord_5698995) baseStart_5698995 baseEnd_5698995 := by
    simpa [prefixWord, tailWord_5698995, baseEnd_5698995] using wordTrace_append hprefix tailTrace_5698995
  have hstable : (prefixWord ++ tailWord_5698995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5698995).length < 2 ^ (prefixWord ++ tailWord_5698995).sum := by decide
  have hdescent : baseEnd_5698995 < baseStart_5698995 := by decide
  rcases family_descends (prefixWord ++ tailWord_5698995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5699012 : List Nat := [2, 3, 3, 2, 1, 1, 1, 2, 3, 2, 3]
def baseStart_5699012 : Nat := 118140960795 + 5699012 * 2 ^ 59
def prefixEnd_5699012 : Nat := 4983230072969 + 3 ^ 40 * 5699012 * 2
def baseEnd_5699012 : Nat := 2926332411741161823040727

theorem tailTrace_5699012 : CollatzResearch.WordTrace tailWord_5699012 prefixEnd_5699012 2926332411741161823040727 := by
  unfold tailWord_5699012
  simp only [CollatzResearch.WordTrace]
  refine ⟨103930022014730156302621645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138573362686306875070162193 103930022014730156302621645)
  ·
    refine ⟨38973758255523808613483117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103930022014730156302621645 38973758255523808613483117)
    ·
      refine ⟨14615159345821428230056169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38973758255523808613483117 14615159345821428230056169)
      ·
        refine ⟨10961369509366071172542127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14615159345821428230056169 10961369509366071172542127)
        ·
          refine ⟨16442054264049106758813191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10961369509366071172542127 16442054264049106758813191)
          ·
            refine ⟨24663081396073660138219787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16442054264049106758813191 24663081396073660138219787)
            ·
              refine ⟨36994622094110490207329681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24663081396073660138219787 36994622094110490207329681)
              ·
                refine ⟨27745966570582867655497261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36994622094110490207329681 27745966570582867655497261)
                ·
                  refine ⟨10404737463968575370811473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27745966570582867655497261 10404737463968575370811473)
                  ·
                    refine ⟨7803553097976431528108605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10404737463968575370811473 7803553097976431528108605)
                    ·
                      refine ⟨2926332411741161823040727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7803553097976431528108605 2926332411741161823040727)
                      ·
                        rfl

theorem cell23_5699012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_5699012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5699012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5699012 prefixEnd_5699012 := by exact prefixLift 5699012
  have htrace : WordTrace (prefixWord ++ tailWord_5699012) baseStart_5699012 baseEnd_5699012 := by
    simpa [prefixWord, tailWord_5699012, baseEnd_5699012] using wordTrace_append hprefix tailTrace_5699012
  have hstable : (prefixWord ++ tailWord_5699012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5699012).length < 2 ^ (prefixWord ++ tailWord_5699012).sum := by decide
  have hdescent : baseEnd_5699012 < baseStart_5699012 := by decide
  rcases family_descends (prefixWord ++ tailWord_5699012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5699025 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 8, 1, 3]
def baseStart_5699025 : Nat := 118140960795 + 5699025 * 2 ^ 59
def prefixEnd_5699025 : Nat := 4983230072969 + 3 ^ 40 * 5699025 * 2
def baseEnd_5699025 : Nat := 2926339086989670272178167

theorem tailTrace_5699025 : CollatzResearch.WordTrace tailWord_5699025 prefixEnd_5699025 2926339086989670272178167 := by
  unfold tailWord_5699025
  simp only [CollatzResearch.WordTrace]
  refine ⟨207860518178413215825466529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138573678785608810550311019 207860518178413215825466529)
  ·
    refine ⟨155895388633809911869099897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207860518178413215825466529 155895388633809911869099897)
    ·
      refine ⟨116921541475357433901824923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155895388633809911869099897 116921541475357433901824923)
      ·
        refine ⟨175382312213036150852737385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116921541475357433901824923 175382312213036150852737385)
        ·
          refine ⟨131536734159777113139553039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175382312213036150852737385 131536734159777113139553039)
          ·
            refine ⟨197305101239665669709329559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131536734159777113139553039 197305101239665669709329559)
            ·
              refine ⟨295957651859498504563994339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197305101239665669709329559 295957651859498504563994339)
              ·
                refine ⟨443936477789247756845991509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 295957651859498504563994339 443936477789247756845991509)
                ·
                  refine ⟨5202380599092747150538963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 443936477789247756845991509 5202380599092747150538963)
                  ·
                    refine ⟨7803570898639120725808445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5202380599092747150538963 7803570898639120725808445)
                    ·
                      refine ⟨2926339086989670272178167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7803570898639120725808445 2926339086989670272178167)
                      ·
                        rfl

theorem cell23_5699025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 8, 1, 3].length) (baseStart_5699025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5699025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5699025 prefixEnd_5699025 := by exact prefixLift 5699025
  have htrace : WordTrace (prefixWord ++ tailWord_5699025) baseStart_5699025 baseEnd_5699025 := by
    simpa [prefixWord, tailWord_5699025, baseEnd_5699025] using wordTrace_append hprefix tailTrace_5699025
  have hstable : (prefixWord ++ tailWord_5699025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5699025).length < 2 ^ (prefixWord ++ tailWord_5699025).sum := by decide
  have hdescent : baseEnd_5699025 < baseStart_5699025 := by decide
  rcases family_descends (prefixWord ++ tailWord_5699025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5699076 : List Nat := [2, 3, 2, 3, 3, 1, 1, 1, 1, 3, 3]
def baseStart_5699076 : Nat := 118140960795 + 5699076 * 2 ^ 59
def prefixEnd_5699076 : Nat := 4983230072969 + 3 ^ 40 * 5699076 * 2
def baseEnd_5699076 : Nat := 2926365274503049572640433

theorem tailTrace_5699076 : CollatzResearch.WordTrace tailWord_5699076 prefixEnd_5699076 2926365274503049572640433 := by
  unfold tailWord_5699076
  simp only [CollatzResearch.WordTrace]
  refine ⟨103931189150614225767786541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138574918867485634357048721 103931189150614225767786541)
  ·
    refine ⟨38974195931480334662919953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103931189150614225767786541 38974195931480334662919953)
    ·
      refine ⟨29230646948610250997189965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38974195931480334662919953 29230646948610250997189965)
      ·
        refine ⟨10961492605728844123946237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29230646948610250997189965 10961492605728844123946237)
        ·
          refine ⟨4110559727148316546479839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10961492605728844123946237 4110559727148316546479839)
          ·
            refine ⟨6165839590722474819719759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4110559727148316546479839 6165839590722474819719759)
            ·
              refine ⟨9248759386083712229579639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6165839590722474819719759 9248759386083712229579639)
              ·
                refine ⟨13873139079125568344369459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9248759386083712229579639 13873139079125568344369459)
                ·
                  refine ⟨20809708618688352516554189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13873139079125568344369459 20809708618688352516554189)
                  ·
                    refine ⟨7803640732008132193707821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20809708618688352516554189 7803640732008132193707821)
                    ·
                      refine ⟨2926365274503049572640433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7803640732008132193707821 2926365274503049572640433)
                      ·
                        rfl

theorem cell23_5699076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_5699076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5699076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5699076 prefixEnd_5699076 := by exact prefixLift 5699076
  have htrace : WordTrace (prefixWord ++ tailWord_5699076) baseStart_5699076 baseEnd_5699076 := by
    simpa [prefixWord, tailWord_5699076, baseEnd_5699076] using wordTrace_append hprefix tailTrace_5699076
  have hstable : (prefixWord ++ tailWord_5699076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5699076).length < 2 ^ (prefixWord ++ tailWord_5699076).sum := by decide
  have hdescent : baseEnd_5699076 < baseStart_5699076 := by decide
  rcases family_descends (prefixWord ++ tailWord_5699076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5699086 : List Nat := [4, 1, 1, 2, 4, 1, 2, 2, 1, 3, 2]
def baseStart_5699086 : Nat := 118140960795 + 5699086 * 2 ^ 59
def prefixEnd_5699086 : Nat := 4983230072969 + 3 ^ 40 * 5699086 * 2
def baseEnd_5699086 : Nat := 2926370409309594533515387

theorem tailTrace_5699086 : CollatzResearch.WordTrace tailWord_5699086 prefixEnd_5699086 2926370409309594533515387 := by
  unfold tailWord_5699086
  simp only [CollatzResearch.WordTrace]
  refine ⟨25982842878899027905429639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138575162020794815495624741 25982842878899027905429639)
  ·
    refine ⟨38974264318348541858144459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25982842878899027905429639 38974264318348541858144459)
    ·
      refine ⟨58461396477522812787216689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38974264318348541858144459 58461396477522812787216689)
      ·
        refine ⟨43846047358142109590412517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58461396477522812787216689 43846047358142109590412517)
        ·
          refine ⟨8221133879651645548202347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43846047358142109590412517 8221133879651645548202347)
          ·
            refine ⟨12331700819477468322303521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8221133879651645548202347 12331700819477468322303521)
            ·
              refine ⟨9248775614608101241727641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12331700819477468322303521 9248775614608101241727641)
              ·
                refine ⟨6936581710956075931295731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9248775614608101241727641 6936581710956075931295731)
                ·
                  refine ⟨10404872566434113896943597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6936581710956075931295731 10404872566434113896943597)
                  ·
                    refine ⟨3901827212412792711353849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10404872566434113896943597 3901827212412792711353849)
                    ·
                      refine ⟨2926370409309594533515387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3901827212412792711353849 2926370409309594533515387)
                      ·
                        rfl

theorem cell23_5699086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 2, 1, 3, 2].length) (baseStart_5699086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5699086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5699086 prefixEnd_5699086 := by exact prefixLift 5699086
  have htrace : WordTrace (prefixWord ++ tailWord_5699086) baseStart_5699086 baseEnd_5699086 := by
    simpa [prefixWord, tailWord_5699086, baseEnd_5699086] using wordTrace_append hprefix tailTrace_5699086
  have hstable : (prefixWord ++ tailWord_5699086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5699086).length < 2 ^ (prefixWord ++ tailWord_5699086).sum := by decide
  have hdescent : baseEnd_5699086 < baseStart_5699086 := by decide
  rcases family_descends (prefixWord ++ tailWord_5699086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5699172 : List Nat := [2, 3, 1, 1, 2, 3, 2, 2, 2, 1, 4]
def baseStart_5699172 : Nat := 118140960795 + 5699172 * 2 ^ 59
def prefixEnd_5699172 : Nat := 4983230072969 + 3 ^ 40 * 5699172 * 2
def baseEnd_5699172 : Nat := 2926414568645881197039991

theorem tailTrace_5699172 : CollatzResearch.WordTrace tailWord_5699172 prefixEnd_5699172 2926414568645881197039991 := by
  unfold tailWord_5699172
  simp only [CollatzResearch.WordTrace]
  refine ⟨103932939854440329965533885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138577253139253773287378513 103932939854440329965533885)
  ·
    refine ⟨38974852445415123737075207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103932939854440329965533885 38974852445415123737075207)
    ·
      refine ⟨58462278668122685605612811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38974852445415123737075207 58462278668122685605612811)
      ·
        refine ⟨87693418002184028408419217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58462278668122685605612811 87693418002184028408419217)
        ·
          refine ⟨65770063501638021306314413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87693418002184028408419217 65770063501638021306314413)
          ·
            refine ⟨24663773813114257989867905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65770063501638021306314413 24663773813114257989867905)
            ·
              refine ⟨18497830359835693492400929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24663773813114257989867905 18497830359835693492400929)
              ·
                refine ⟨13873372769876770119300697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18497830359835693492400929 13873372769876770119300697)
                ·
                  refine ⟨10405029577407577589475523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13873372769876770119300697 10405029577407577589475523)
                  ·
                    refine ⟨15607544366111366384213285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10405029577407577589475523 15607544366111366384213285)
                    ·
                      refine ⟨2926414568645881197039991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15607544366111366384213285 2926414568645881197039991)
                      ·
                        rfl

theorem cell23_5699172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2, 2, 1, 4].length) (baseStart_5699172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5699172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5699172 prefixEnd_5699172 := by exact prefixLift 5699172
  have htrace : WordTrace (prefixWord ++ tailWord_5699172) baseStart_5699172 baseEnd_5699172 := by
    simpa [prefixWord, tailWord_5699172, baseEnd_5699172] using wordTrace_append hprefix tailTrace_5699172
  have hstable : (prefixWord ++ tailWord_5699172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5699172).length < 2 ^ (prefixWord ++ tailWord_5699172).sum := by decide
  have hdescent : baseEnd_5699172 < baseStart_5699172 := by decide
  rcases family_descends (prefixWord ++ tailWord_5699172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5699189 : List Nat := [1, 3, 4, 2, 1, 1, 1, 1, 1, 6, 2]
def baseStart_5699189 : Nat := 118140960795 + 5699189 * 2 ^ 59
def prefixEnd_5699189 : Nat := 4983230072969 + 3 ^ 40 * 5699189 * 2
def baseEnd_5699189 : Nat := 2926423297817007630527413

theorem tailTrace_5699189 : CollatzResearch.WordTrace tailWord_5699189 prefixEnd_5699189 2926423297817007630527413 := by
  unfold tailWord_5699189
  simp only [CollatzResearch.WordTrace]
  refine ⟨207866499749819071834436621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138577666499879381222957747 207866499749819071834436621)
  ·
    refine ⟨77949937406182151937913733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207866499749819071834436621 77949937406182151937913733)
    ·
      refine ⟨14615613263659153488358825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77949937406182151937913733 14615613263659153488358825)
      ·
        refine ⟨10961709947744365116269119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14615613263659153488358825 10961709947744365116269119)
        ·
          refine ⟨16442564921616547674403679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10961709947744365116269119 16442564921616547674403679)
          ·
            refine ⟨24663847382424821511605519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16442564921616547674403679 24663847382424821511605519)
            ·
              refine ⟨36995771073637232267408279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24663847382424821511605519 36995771073637232267408279)
              ·
                refine ⟨55493656610455848401112419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36995771073637232267408279 55493656610455848401112419)
                ·
                  refine ⟨83240484915683772601668629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55493656610455848401112419 83240484915683772601668629)
                  ·
                    refine ⟨3901897730422676840703217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 83240484915683772601668629 3901897730422676840703217)
                    ·
                      refine ⟨2926423297817007630527413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3901897730422676840703217 2926423297817007630527413)
                      ·
                        rfl

theorem cell23_5699189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_5699189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5699189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5699189 prefixEnd_5699189 := by exact prefixLift 5699189
  have htrace : WordTrace (prefixWord ++ tailWord_5699189) baseStart_5699189 baseEnd_5699189 := by
    simpa [prefixWord, tailWord_5699189, baseEnd_5699189] using wordTrace_append hprefix tailTrace_5699189
  have hstable : (prefixWord ++ tailWord_5699189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5699189).length < 2 ^ (prefixWord ++ tailWord_5699189).sum := by decide
  have hdescent : baseEnd_5699189 < baseStart_5699189 := by decide
  rcases family_descends (prefixWord ++ tailWord_5699189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5699195 : List Nat := [1, 1, 1, 1, 1, 4, 3, 5, 6]
def baseStart_5699195 : Nat := 118140960795 + 5699195 * 2 ^ 59
def prefixEnd_5699195 : Nat := 4983230072969 + 3 ^ 40 * 5699195 * 2
def baseEnd_5699195 : Nat := 325158486522326067450265

theorem tailTrace_5699195 : CollatzResearch.WordTrace tailWord_5699195 prefixEnd_5699195 325158486522326067450265 := by
  unfold tailWord_5699195
  simp only [CollatzResearch.WordTrace]
  refine ⟨207866718587797334859155039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138577812391864889906103359 207866718587797334859155039)
  ·
    refine ⟨311800077881696002288732559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207866718587797334859155039 311800077881696002288732559)
    ·
      refine ⟨467700116822544003433098839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311800077881696002288732559 467700116822544003433098839)
      ·
        refine ⟨701550175233816005149648259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 467700116822544003433098839 701550175233816005149648259)
        ·
          refine ⟨1052325262850724007724472389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 701550175233816005149648259 1052325262850724007724472389)
          ·
            refine ⟨197310986784510751448338573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1052325262850724007724472389 197310986784510751448338573)
            ·
              refine ⟨73991620044191531793126965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 197310986784510751448338573 73991620044191531793126965)
              ·
                refine ⟨6936714379142956105605653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73991620044191531793126965 6936714379142956105605653)
                ·
                  refine ⟨325158486522326067450265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6936714379142956105605653 325158486522326067450265)
                  ·
                    rfl

theorem cell23_5699195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 5, 6].length) (baseStart_5699195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5699195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5699195 prefixEnd_5699195 := by exact prefixLift 5699195
  have htrace : WordTrace (prefixWord ++ tailWord_5699195) baseStart_5699195 baseEnd_5699195 := by
    simpa [prefixWord, tailWord_5699195, baseEnd_5699195] using wordTrace_append hprefix tailTrace_5699195
  have hstable : (prefixWord ++ tailWord_5699195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5699195).length < 2 ^ (prefixWord ++ tailWord_5699195).sum := by decide
  have hdescent : baseEnd_5699195 < baseStart_5699195 := by decide
  rcases family_descends (prefixWord ++ tailWord_5699195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5699225 : List Nat := [1, 2, 1, 2, 1, 2, 2, 2, 5, 5]
def baseStart_5699225 : Nat := 118140960795 + 5699225 * 2 ^ 59
def prefixEnd_5699225 : Nat := 4983230072969 + 3 ^ 40 * 5699225 * 2
def baseEnd_5699225 : Nat := 975480594373523163225749

theorem tailTrace_5699225 : CollatzResearch.WordTrace tailWord_5699225 prefixEnd_5699225 975480594373523163225749 := by
  unfold tailWord_5699225
  simp only [CollatzResearch.WordTrace]
  refine ⟨207867812777688649982747129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138578541851792433321831419 207867812777688649982747129)
  ·
    refine ⟨155900859583266487487060347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207867812777688649982747129 155900859583266487487060347)
    ·
      refine ⟨233851289374899731230590521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155900859583266487487060347 233851289374899731230590521)
      ·
        refine ⟨175388467031174798422942891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233851289374899731230590521 175388467031174798422942891)
        ·
          refine ⟨263082700546762197634414337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175388467031174798422942891 263082700546762197634414337)
          ·
            refine ⟨197312025410071648225810753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 263082700546762197634414337 197312025410071648225810753)
            ·
              refine ⟨147984019057553736169358065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197312025410071648225810753 147984019057553736169358065)
              ·
                refine ⟨110988014293165302127018549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147984019057553736169358065 110988014293165302127018549)
                ·
                  refine ⟨10405126339984247074407989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 110988014293165302127018549 10405126339984247074407989)
                  ·
                    refine ⟨975480594373523163225749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10405126339984247074407989 975480594373523163225749)
                    ·
                      rfl

theorem cell23_5699225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 5, 5].length) (baseStart_5699225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5699225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5699225 prefixEnd_5699225 := by exact prefixLift 5699225
  have htrace : WordTrace (prefixWord ++ tailWord_5699225) baseStart_5699225 baseEnd_5699225 := by
    simpa [prefixWord, tailWord_5699225, baseEnd_5699225] using wordTrace_append hprefix tailTrace_5699225
  have hstable : (prefixWord ++ tailWord_5699225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5699225).length < 2 ^ (prefixWord ++ tailWord_5699225).sum := by decide
  have hdescent : baseEnd_5699225 < baseStart_5699225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5699225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5699272 : List Nat := [2, 1, 3, 1, 2, 2, 1, 1, 6, 4]
def baseStart_5699272 : Nat := 118140960795 + 5699272 * 2 ^ 59
def prefixEnd_5699272 : Nat := 4983230072969 + 3 ^ 40 * 5699272 * 2
def baseEnd_5699272 : Nat := 975488638903776935263177

theorem tailTrace_5699272 : CollatzResearch.WordTrace tailWord_5699272 prefixEnd_5699272 975488638903776935263177 := by
  unfold tailWord_5699272
  simp only [CollatzResearch.WordTrace]
  refine ⟨103934763504259188504854035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138579684672345584673138713 103934763504259188504854035)
  ·
    refine ⟨155902145256388782757281053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103934763504259188504854035 155902145256388782757281053)
    ·
      refine ⟨58463304471145793533980395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155902145256388782757281053 58463304471145793533980395)
      ·
        refine ⟨87694956706718690300970593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58463304471145793533980395 87694956706718690300970593)
        ·
          refine ⟨65771217530039017725727945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87694956706718690300970593 65771217530039017725727945)
          ·
            refine ⟨49328413147529263294295959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65771217530039017725727945 49328413147529263294295959)
            ·
              refine ⟨73992619721293894941443939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49328413147529263294295959 73992619721293894941443939)
              ·
                refine ⟨110988929581940842412165909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73992619721293894941443939 110988929581940842412165909)
                ·
                  refine ⟨5202606074153476988070277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 110988929581940842412165909 5202606074153476988070277)
                  ·
                    refine ⟨975488638903776935263177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5202606074153476988070277 975488638903776935263177)
                    ·
                      rfl

theorem cell23_5699272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 6, 4].length) (baseStart_5699272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5699272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5699272 prefixEnd_5699272 := by exact prefixLift 5699272
  have htrace : WordTrace (prefixWord ++ tailWord_5699272) baseStart_5699272 baseEnd_5699272 := by
    simpa [prefixWord, tailWord_5699272, baseEnd_5699272] using wordTrace_append hprefix tailTrace_5699272
  have hstable : (prefixWord ++ tailWord_5699272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5699272).length < 2 ^ (prefixWord ++ tailWord_5699272).sum := by decide
  have hdescent : baseEnd_5699272 < baseStart_5699272 := by decide
  rcases family_descends (prefixWord ++ tailWord_5699272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5699279 : List Nat := [1, 1, 2, 1, 1, 3, 1, 4, 5, 2, 2]
def baseStart_5699279 : Nat := 118140960795 + 5699279 * 2 ^ 59
def prefixEnd_5699279 : Nat := 4983230072969 + 3 ^ 40 * 5699279 * 2
def baseEnd_5699279 : Nat := 2926469511075912278401999

theorem tailTrace_5699279 : CollatzResearch.WordTrace tailWord_5699279 prefixEnd_5699279 2926469511075912278401999 := by
  unfold tailWord_5699279
  simp only [CollatzResearch.WordTrace]
  refine ⟨207869782319493017205212891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138579854879662011470141927 207869782319493017205212891)
  ·
    refine ⟨311804673479239525807819337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207869782319493017205212891 311804673479239525807819337)
    ·
      refine ⟨233853505109429644355864503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311804673479239525807819337 233853505109429644355864503)
      ·
        refine ⟨350780257664144466533796755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233853505109429644355864503 350780257664144466533796755)
        ·
          refine ⟨526170386496216699800695133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350780257664144466533796755 526170386496216699800695133)
          ·
            refine ⟨197313894936081262425260675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 526170386496216699800695133 197313894936081262425260675)
            ·
              refine ⟨295970842404121893637891013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197313894936081262425260675 295970842404121893637891013)
              ·
                refine ⟨55494532950772855057104565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 295970842404121893637891013 55494532950772855057104565)
                ·
                  refine ⟨5202612464134955161603553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55494532950772855057104565 5202612464134955161603553)
                  ·
                    refine ⟨3901959348101216371202665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5202612464134955161603553 3901959348101216371202665)
                    ·
                      refine ⟨2926469511075912278401999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3901959348101216371202665 2926469511075912278401999)
                      ·
                        rfl

theorem cell23_5699279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 5, 2, 2].length) (baseStart_5699279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5699279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5699279 prefixEnd_5699279 := by exact prefixLift 5699279
  have htrace : WordTrace (prefixWord ++ tailWord_5699279) baseStart_5699279 baseEnd_5699279 := by
    simpa [prefixWord, tailWord_5699279, baseEnd_5699279] using wordTrace_append hprefix tailTrace_5699279
  have hstable : (prefixWord ++ tailWord_5699279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5699279).length < 2 ^ (prefixWord ++ tailWord_5699279).sum := by decide
  have hdescent : baseEnd_5699279 < baseStart_5699279 := by decide
  rcases family_descends (prefixWord ++ tailWord_5699279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5699296 : List Nat := [2, 1, 1, 3, 1, 2, 5, 1, 3, 2, 2]
def baseStart_5699296 : Nat := 118140960795 + 5699296 * 2 ^ 59
def prefixEnd_5699296 : Nat := 4983230072969 + 3 ^ 40 * 5699296 * 2
def baseEnd_5699296 : Nat := 2926478240247038711889421

theorem tailTrace_5699296 : CollatzResearch.WordTrace tailWord_5699296 prefixEnd_5699296 2926478240247038711889421 := by
  unfold tailWord_5699296
  simp only [CollatzResearch.WordTrace]
  refine ⟨103935201180215714554290871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138580268240287619405721161 103935201180215714554290871)
  ·
    refine ⟨155902801770323571831436307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103935201180215714554290871 155902801770323571831436307)
    ·
      refine ⟨233854202655485357747154461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155902801770323571831436307 233854202655485357747154461)
      ·
        refine ⟨87695325995807009155182923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 233854202655485357747154461 87695325995807009155182923)
        ·
          refine ⟨131542988993710513732774385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87695325995807009155182923 131542988993710513732774385)
          ·
            refine ⟨98657241745282885299580789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131542988993710513732774385 98657241745282885299580789)
            ·
              refine ⟨9249116413620270496835699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 98657241745282885299580789 9249116413620270496835699)
              ·
                refine ⟨13873674620430405745253549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9249116413620270496835699 13873674620430405745253549)
                ·
                  refine ⟨5202627982661402154470081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13873674620430405745253549 5202627982661402154470081)
                  ·
                    refine ⟨3901970986996051615852561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5202627982661402154470081 3901970986996051615852561)
                    ·
                      refine ⟨2926478240247038711889421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3901970986996051615852561 2926478240247038711889421)
                      ·
                        rfl

theorem cell23_5699296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 1, 3, 2, 2].length) (baseStart_5699296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5699296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5699296 prefixEnd_5699296 := by exact prefixLift 5699296
  have htrace : WordTrace (prefixWord ++ tailWord_5699296) baseStart_5699296 baseEnd_5699296 := by
    simpa [prefixWord, tailWord_5699296, baseEnd_5699296] using wordTrace_append hprefix tailTrace_5699296
  have hstable : (prefixWord ++ tailWord_5699296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5699296).length < 2 ^ (prefixWord ++ tailWord_5699296).sum := by decide
  have hdescent : baseEnd_5699296 < baseStart_5699296 := by decide
  rcases family_descends (prefixWord ++ tailWord_5699296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5699305 : List Nat := [1, 2, 1, 1, 1, 2, 3, 1, 1, 4, 6]
def baseStart_5699305 : Nat := 118140960795 + 5699305 * 2 ^ 59
def prefixEnd_5699305 : Nat := 4983230072969 + 3 ^ 40 * 5699305 * 2
def baseEnd_5699305 : Nat := 2926482861572929176676879

theorem tailTrace_5699305 : CollatzResearch.WordTrace tailWord_5699305 prefixEnd_5699305 2926482861572929176676879 := by
  unfold tailWord_5699305
  simp only [CollatzResearch.WordTrace]
  refine ⟨207870730617398823645659369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138580487078265882430439579 207870730617398823645659369)
  ·
    refine ⟨155903047963049117734244527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207870730617398823645659369 155903047963049117734244527)
    ·
      refine ⟨233854571944573676601366791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155903047963049117734244527 233854571944573676601366791)
      ·
        refine ⟨350781857916860514902050187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233854571944573676601366791 350781857916860514902050187)
        ·
          refine ⟨526172786875290772353075281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350781857916860514902050187 526172786875290772353075281)
          ·
            refine ⟨394629590156468079264806461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 526172786875290772353075281 394629590156468079264806461)
            ·
              refine ⟨147986096308675529724302423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 394629590156468079264806461 147986096308675529724302423)
              ·
                refine ⟨221979144463013294586453635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147986096308675529724302423 221979144463013294586453635)
                ·
                  refine ⟨332968716694519941879680453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 221979144463013294586453635 332968716694519941879680453)
                  ·
                    refine ⟨62431634380222489102440085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 332968716694519941879680453 62431634380222489102440085)
                    ·
                      refine ⟨2926482861572929176676879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62431634380222489102440085 2926482861572929176676879)
                      ·
                        rfl

theorem cell23_5699305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 4, 6].length) (baseStart_5699305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5699305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5699305 prefixEnd_5699305 := by exact prefixLift 5699305
  have htrace : WordTrace (prefixWord ++ tailWord_5699305) baseStart_5699305 baseEnd_5699305 := by
    simpa [prefixWord, tailWord_5699305, baseEnd_5699305] using wordTrace_append hprefix tailTrace_5699305
  have hstable : (prefixWord ++ tailWord_5699305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5699305).length < 2 ^ (prefixWord ++ tailWord_5699305).sum := by decide
  have hdescent : baseEnd_5699305 < baseStart_5699305 := by decide
  rcases family_descends (prefixWord ++ tailWord_5699305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5699306 : List Nat := [3, 1, 3, 1, 1, 1, 6, 1, 2, 4]
def baseStart_5699306 : Nat := 118140960795 + 5699306 * 2 ^ 59
def prefixEnd_5699306 : Nat := 4983230072969 + 3 ^ 40 * 5699306 * 2
def baseEnd_5699306 : Nat := 975494458351194557588125

theorem tailTrace_5699306 : CollatzResearch.WordTrace tailWord_5699306 prefixEnd_5699306 975494458351194557588125 := by
  unfold tailWord_5699306
  simp only [CollatzResearch.WordTrace]
  refine ⟨51967691772598800204111443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138580511393596800544297181 51967691772598800204111443)
  ·
    refine ⟨77951537658898200306167165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51967691772598800204111443 77951537658898200306167165)
    ·
      refine ⟨29231826622086825114812687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77951537658898200306167165 29231826622086825114812687)
      ·
        refine ⟨43847739933130237672219031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29231826622086825114812687 43847739933130237672219031)
        ·
          refine ⟨65771609899695356508328547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43847739933130237672219031 65771609899695356508328547)
          ·
            refine ⟨98657414849543034762492821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65771609899695356508328547 98657414849543034762492821)
            ·
              refine ⟨4624566321072329754491851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 98657414849543034762492821 4624566321072329754491851)
              ·
                refine ⟨6936849481608494631737777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4624566321072329754491851 6936849481608494631737777)
                ·
                  refine ⟨5202637111206370973803333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6936849481608494631737777 5202637111206370973803333)
                  ·
                    refine ⟨975494458351194557588125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5202637111206370973803333 975494458351194557588125)
                    ·
                      rfl

theorem cell23_5699306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 1, 2, 4].length) (baseStart_5699306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5699306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5699306 prefixEnd_5699306 := by exact prefixLift 5699306
  have htrace : WordTrace (prefixWord ++ tailWord_5699306) baseStart_5699306 baseEnd_5699306 := by
    simpa [prefixWord, tailWord_5699306, baseEnd_5699306] using wordTrace_append hprefix tailTrace_5699306
  have hstable : (prefixWord ++ tailWord_5699306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5699306).length < 2 ^ (prefixWord ++ tailWord_5699306).sum := by decide
  have hdescent : baseEnd_5699306 < baseStart_5699306 := by decide
  rcases family_descends (prefixWord ++ tailWord_5699306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5699326 : List Nat := [4, 2, 2, 1, 3, 1, 1, 2, 1, 2, 4]
def baseStart_5699326 : Nat := 118140960795 + 5699326 * 2 ^ 59
def prefixEnd_5699326 : Nat := 4983230072969 + 3 ^ 40 * 5699326 * 2
def baseEnd_5699326 : Nat := 2926493644666673594514283

theorem tailTrace_5699326 : CollatzResearch.WordTrace tailWord_5699326 prefixEnd_5699326 2926493644666673594514283 := by
  unfold tailWord_5699326
  simp only [CollatzResearch.WordTrace]
  refine ⟨25983937068790343029021729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138580997700215162821449221 25983937068790343029021729)
  ·
    refine ⟨19487952801592757271766297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25983937068790343029021729 19487952801592757271766297)
    ·
      refine ⟨14615964601194567953824723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19487952801592757271766297 14615964601194567953824723)
      ·
        refine ⟨21923946901791851930737085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14615964601194567953824723 21923946901791851930737085)
        ·
          refine ⟨8221480088171944474026407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21923946901791851930737085 8221480088171944474026407)
          ·
            refine ⟨12332220132257916711039611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8221480088171944474026407 12332220132257916711039611)
            ·
              refine ⟨18498330198386875066559417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12332220132257916711039611 18498330198386875066559417)
              ·
                refine ⟨13873747648790156299919563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18498330198386875066559417 13873747648790156299919563)
                ·
                  refine ⟨20810621473185234449879345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13873747648790156299919563 20810621473185234449879345)
                  ·
                    refine ⟨15607966104888925837409509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20810621473185234449879345 15607966104888925837409509)
                    ·
                      refine ⟨2926493644666673594514283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15607966104888925837409509 2926493644666673594514283)
                      ·
                        rfl

theorem cell23_5699326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_5699326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5699326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5699326 prefixEnd_5699326 := by exact prefixLift 5699326
  have htrace : WordTrace (prefixWord ++ tailWord_5699326) baseStart_5699326 baseEnd_5699326 := by
    simpa [prefixWord, tailWord_5699326, baseEnd_5699326] using wordTrace_append hprefix tailTrace_5699326
  have hstable : (prefixWord ++ tailWord_5699326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5699326).length < 2 ^ (prefixWord ++ tailWord_5699326).sum := by decide
  have hdescent : baseEnd_5699326 < baseStart_5699326 := by decide
  rcases family_descends (prefixWord ++ tailWord_5699326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5699329 : List Nat := [1, 2, 4, 1, 1, 1, 2, 1, 6, 1, 3]
def baseStart_5699329 : Nat := 118140960795 + 5699329 * 2 ^ 59
def prefixEnd_5699329 : Nat := 4983230072969 + 3 ^ 40 * 5699329 * 2
def baseEnd_5699329 : Nat := 2926495185108637082776769

theorem tailTrace_5699329 : CollatzResearch.WordTrace tailWord_5699329 prefixEnd_5699329 2926495185108637082776769 := by
  unfold tailWord_5699329
  simp only [CollatzResearch.WordTrace]
  refine ⟨207871605969311875744533041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138581070646207917163022027 207871605969311875744533041)
  ·
    refine ⟨155903704476983906808399781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207871605969311875744533041 155903704476983906808399781)
    ·
      refine ⟨29231944589434482526574959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 155903704476983906808399781 29231944589434482526574959)
      ·
        refine ⟨43847916884151723789862439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29231944589434482526574959 43847916884151723789862439)
        ·
          refine ⟨65771875326227585684793659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43847916884151723789862439 65771875326227585684793659)
          ·
            refine ⟨98657812989341378527190489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65771875326227585684793659 98657812989341378527190489)
            ·
              refine ⟨73993359742006033895392867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98657812989341378527190489 73993359742006033895392867)
              ·
                refine ⟨110990039613009050843089301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73993359742006033895392867 110990039613009050843089301)
                ·
                  refine ⟨5202658106859799258269811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 110990039613009050843089301 5202658106859799258269811)
                  ·
                    refine ⟨7803987160289698887404717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5202658106859799258269811 7803987160289698887404717)
                    ·
                      refine ⟨2926495185108637082776769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7803987160289698887404717 2926495185108637082776769)
                      ·
                        rfl

theorem cell23_5699329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 6, 1, 3].length) (baseStart_5699329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5699329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5699329 prefixEnd_5699329 := by exact prefixLift 5699329
  have htrace : WordTrace (prefixWord ++ tailWord_5699329) baseStart_5699329 baseEnd_5699329 := by
    simpa [prefixWord, tailWord_5699329, baseEnd_5699329] using wordTrace_append hprefix tailTrace_5699329
  have hstable : (prefixWord ++ tailWord_5699329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5699329).length < 2 ^ (prefixWord ++ tailWord_5699329).sum := by decide
  have hdescent : baseEnd_5699329 < baseStart_5699329 := by decide
  rcases family_descends (prefixWord ++ tailWord_5699329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5699330 : List Nat := [3, 4, 1, 1, 1, 1, 2, 5, 1, 2, 2]
def baseStart_5699330 : Nat := 118140960795 + 5699330 * 2 ^ 59
def prefixEnd_5699330 : Nat := 4983230072969 + 3 ^ 40 * 5699330 * 2
def baseEnd_5699330 : Nat := 2926495698589291578864265

theorem tailTrace_5699330 : CollatzResearch.WordTrace tailWord_5699330 prefixEnd_5699330 2926495698589291578864265 := by
  unfold tailWord_5699330
  simp only [CollatzResearch.WordTrace]
  refine ⟨51967910610577063228829861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138581094961538835276879629 51967910610577063228829861)
  ·
    refine ⟨9743983239483199355405599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51967910610577063228829861 9743983239483199355405599)
    ·
      refine ⟨14615974859224799033108399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9743983239483199355405599 14615974859224799033108399)
      ·
        refine ⟨21923962288837198549662599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14615974859224799033108399 21923962288837198549662599)
        ·
          refine ⟨32885943433255797824493899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21923962288837198549662599 32885943433255797824493899)
          ·
            refine ⟨49328915149883696736740849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32885943433255797824493899 49328915149883696736740849)
            ·
              refine ⟨36996686362412772552555637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49328915149883696736740849 36996686362412772552555637)
              ·
                refine ⟨3468439346476197426802091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36996686362412772552555637 3468439346476197426802091)
                ·
                  refine ⟨5202659019714296140203137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3468439346476197426802091 5202659019714296140203137)
                  ·
                    refine ⟨3901994264785722105152353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5202659019714296140203137 3901994264785722105152353)
                    ·
                      refine ⟨2926495698589291578864265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3901994264785722105152353 2926495698589291578864265)
                      ·
                        rfl

theorem cell23_5699330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_5699330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5699330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5699330 prefixEnd_5699330 := by exact prefixLift 5699330
  have htrace : WordTrace (prefixWord ++ tailWord_5699330) baseStart_5699330 baseEnd_5699330 := by
    simpa [prefixWord, tailWord_5699330, baseEnd_5699330] using wordTrace_append hprefix tailTrace_5699330
  have hstable : (prefixWord ++ tailWord_5699330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5699330).length < 2 ^ (prefixWord ++ tailWord_5699330).sum := by decide
  have hdescent : baseEnd_5699330 < baseStart_5699330 := by decide
  rcases family_descends (prefixWord ++ tailWord_5699330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5699342 : List Nat := [4, 1, 1, 2, 1, 1, 2, 2, 2, 2, 5]
def baseStart_5699342 : Nat := 118140960795 + 5699342 * 2 ^ 59
def prefixEnd_5699342 : Nat := 4983230072969 + 3 ^ 40 * 5699342 * 2
def baseEnd_5699342 : Nat := 2926501860357145531914209

theorem tailTrace_5699342 : CollatzResearch.WordTrace tailWord_5699342 prefixEnd_5699342 2926501860357145531914209 := by
  unfold tailWord_5699342
  simp only [CollatzResearch.WordTrace]
  refine ⟨25984010014783097370594535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138581386745509852643170853 25984010014783097370594535)
  ·
    refine ⟨38976015022174646055891803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25984010014783097370594535 38976015022174646055891803)
    ·
      refine ⟨58464022533261969083837705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38976015022174646055891803 58464022533261969083837705)
      ·
        refine ⟨43848016899946476812878279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58464022533261969083837705 43848016899946476812878279)
        ·
          refine ⟨65772025349919715219317419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43848016899946476812878279 65772025349919715219317419)
          ·
            refine ⟨98658038024879572828976129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65772025349919715219317419 98658038024879572828976129)
            ·
              refine ⟨73993528518659679621732097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98658038024879572828976129 73993528518659679621732097)
              ·
                refine ⟨55495146388994759716299073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73993528518659679621732097 55495146388994759716299073)
                ·
                  refine ⟨41621359791746069787224305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55495146388994759716299073 41621359791746069787224305)
                  ·
                    refine ⟨31216019843809552340418229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41621359791746069787224305 31216019843809552340418229)
                    ·
                      refine ⟨2926501860357145531914209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31216019843809552340418229 2926501860357145531914209)
                      ·
                        rfl

theorem cell23_5699342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_5699342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5699342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5699342 prefixEnd_5699342 := by exact prefixLift 5699342
  have htrace : WordTrace (prefixWord ++ tailWord_5699342) baseStart_5699342 baseEnd_5699342 := by
    simpa [prefixWord, tailWord_5699342, baseEnd_5699342] using wordTrace_append hprefix tailTrace_5699342
  have hstable : (prefixWord ++ tailWord_5699342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5699342).length < 2 ^ (prefixWord ++ tailWord_5699342).sum := by decide
  have hdescent : baseEnd_5699342 < baseStart_5699342 := by decide
  rcases family_descends (prefixWord ++ tailWord_5699342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5699352 : List Nat := [2, 1, 2, 3, 1, 1, 3, 1, 2, 3, 4]
def baseStart_5699352 : Nat := 118140960795 + 5699352 * 2 ^ 59
def prefixEnd_5699352 : Nat := 4983230072969 + 3 ^ 40 * 5699352 * 2
def baseEnd_5699352 : Nat := 2926506995163690492789163

theorem tailTrace_5699352 : CollatzResearch.WordTrace tailWord_5699352 prefixEnd_5699352 2926506995163690492789163 := by
  unfold tailWord_5699352
  simp only [CollatzResearch.WordTrace]
  refine ⟨103936222424114275336310155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138581629898819033781746873 103936222424114275336310155)
  ·
    refine ⟨155904333636171413004465233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103936222424114275336310155 155904333636171413004465233)
    ·
      refine ⟨116928250227128559753348925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155904333636171413004465233 116928250227128559753348925)
      ·
        refine ⟨43848093835173209907505847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116928250227128559753348925 43848093835173209907505847)
        ·
          refine ⟨65772140752759814861258771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43848093835173209907505847 65772140752759814861258771)
          ·
            refine ⟨98658211129139722291888157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65772140752759814861258771 98658211129139722291888157)
            ·
              refine ⟨36996829173427395859458059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98658211129139722291888157 36996829173427395859458059)
              ·
                refine ⟨55495243760141093789187089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36996829173427395859458059 55495243760141093789187089)
                ·
                  refine ⟨41621432820105820341890317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55495243760141093789187089 41621432820105820341890317)
                  ·
                    refine ⟨15608037307539682628208869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41621432820105820341890317 15608037307539682628208869)
                    ·
                      refine ⟨2926506995163690492789163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15608037307539682628208869 2926506995163690492789163)
                      ·
                        rfl

theorem cell23_5699352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_5699352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5699352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5699352 prefixEnd_5699352 := by exact prefixLift 5699352
  have htrace : WordTrace (prefixWord ++ tailWord_5699352) baseStart_5699352 baseEnd_5699352 := by
    simpa [prefixWord, tailWord_5699352, baseEnd_5699352] using wordTrace_append hprefix tailTrace_5699352
  have hstable : (prefixWord ++ tailWord_5699352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5699352).length < 2 ^ (prefixWord ++ tailWord_5699352).sum := by decide
  have hdescent : baseEnd_5699352 < baseStart_5699352 := by decide
  rcases family_descends (prefixWord ++ tailWord_5699352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5699386 : List Nat := [3, 1, 1, 1, 5, 1, 2, 2, 1, 4, 2]
def baseStart_5699386 : Nat := 118140960795 + 5699386 * 2 ^ 59
def prefixEnd_5699386 : Nat := 4983230072969 + 3 ^ 40 * 5699386 * 2
def baseEnd_5699386 : Nat := 2926524453505943359764007

theorem tailTrace_5699386 : CollatzResearch.WordTrace tailWord_5699386 prefixEnd_5699386 2926524453505943359764007 := by
  unfold tailWord_5699386
  simp only [CollatzResearch.WordTrace]
  refine ⟨51968421232526343619839503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138582456620070249652905341 51968421232526343619839503)
  ·
    refine ⟨77952631848789515429759255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51968421232526343619839503 77952631848789515429759255)
    ·
      refine ⟨116928947773184273144638883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77952631848789515429759255 116928947773184273144638883)
      ·
        refine ⟨175393421659776409716958325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116928947773184273144638883 175393421659776409716958325)
        ·
          refine ⟨16443133280604038410964843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 175393421659776409716958325 16443133280604038410964843)
          ·
            refine ⟨24664699920906057616447265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16443133280604038410964843 24664699920906057616447265)
            ·
              refine ⟨18498524940679543212335449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24664699920906057616447265 18498524940679543212335449)
              ·
                refine ⟨13873893705509657409251587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18498524940679543212335449 13873893705509657409251587)
                ·
                  refine ⟨20810840558264486113877381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13873893705509657409251587 20810840558264486113877381)
                  ·
                    refine ⟨3902032604674591146352009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20810840558264486113877381 3902032604674591146352009)
                    ·
                      refine ⟨2926524453505943359764007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3902032604674591146352009 2926524453505943359764007)
                      ·
                        rfl

theorem cell23_5699386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2, 1, 4, 2].length) (baseStart_5699386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5699386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5699386 prefixEnd_5699386 := by exact prefixLift 5699386
  have htrace : WordTrace (prefixWord ++ tailWord_5699386) baseStart_5699386 baseEnd_5699386 := by
    simpa [prefixWord, tailWord_5699386, baseEnd_5699386] using wordTrace_append hprefix tailTrace_5699386
  have hstable : (prefixWord ++ tailWord_5699386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5699386).length < 2 ^ (prefixWord ++ tailWord_5699386).sum := by decide
  have hdescent : baseEnd_5699386 < baseStart_5699386 := by decide
  rcases family_descends (prefixWord ++ tailWord_5699386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5699390 : List Nat := [4, 2, 1, 2, 2, 1, 4, 1, 1, 3, 2]
def baseStart_5699390 : Nat := 118140960795 + 5699390 * 2 ^ 59
def prefixEnd_5699390 : Nat := 4983230072969 + 3 ^ 40 * 5699390 * 2
def baseEnd_5699390 : Nat := 2926526507428561344113989

theorem tailTrace_5699390 : CollatzResearch.WordTrace tailWord_5699390 prefixEnd_5699390 2926526507428561344113989 := by
  unfold tailWord_5699390
  simp only [CollatzResearch.WordTrace]
  refine ⟨25984228852761360395312953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138582553881393922108335749 25984228852761360395312953)
  ·
    refine ⟨19488171639571020296484715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25984228852761360395312953 19488171639571020296484715)
    ·
      refine ⟨29232257459356530444727073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19488171639571020296484715 29232257459356530444727073)
      ·
        refine ⟨21924193094517397833545305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29232257459356530444727073 21924193094517397833545305)
        ·
          refine ⟨16443144820888048375158979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21924193094517397833545305 16443144820888048375158979)
          ·
            refine ⟨24664717231332072562738469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16443144820888048375158979 24664717231332072562738469)
            ·
              refine ⟨4624634480874763605513463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24664717231332072562738469 4624634480874763605513463)
              ·
                refine ⟨6936951721312145408270195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4624634480874763605513463 6936951721312145408270195)
                ·
                  refine ⟨10405427581968218112405293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6936951721312145408270195 10405427581968218112405293)
                  ·
                    refine ⟨3902035343238081792151985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10405427581968218112405293 3902035343238081792151985)
                    ·
                      refine ⟨2926526507428561344113989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3902035343238081792151985 2926526507428561344113989)
                      ·
                        rfl

theorem cell23_5699390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_5699390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5699390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5699390 prefixEnd_5699390 := by exact prefixLift 5699390
  have htrace : WordTrace (prefixWord ++ tailWord_5699390) baseStart_5699390 baseEnd_5699390 := by
    simpa [prefixWord, tailWord_5699390, baseEnd_5699390] using wordTrace_append hprefix tailTrace_5699390
  have hstable : (prefixWord ++ tailWord_5699390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5699390).length < 2 ^ (prefixWord ++ tailWord_5699390).sum := by decide
  have hdescent : baseEnd_5699390 < baseStart_5699390 := by decide
  rcases family_descends (prefixWord ++ tailWord_5699390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5699409 : List Nat := [1, 2, 2, 1, 5, 2, 2, 1, 7]
def baseStart_5699409 : Nat := 118140960795 + 5699409 * 2 ^ 59
def prefixEnd_5699409 : Nat := 4983230072969 + 3 ^ 40 * 5699409 * 2
def baseEnd_5699409 : Nat := 325170695951221863308489

theorem tailTrace_5699409 : CollatzResearch.WordTrace tailWord_5699409 prefixEnd_5699409 325170695951221863308489 := by
  unfold tailWord_5699409
  simp only [CollatzResearch.WordTrace]
  refine ⟨207874523809022049407445281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138583015872681366271630187 207874523809022049407445281)
  ·
    refine ⟨155905892856766537055583961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207874523809022049407445281 155905892856766537055583961)
    ·
      refine ⟨116929419642574902791687971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155905892856766537055583961 116929419642574902791687971)
      ·
        refine ⟨175394129463862354187531957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116929419642574902791687971 175394129463862354187531957)
        ·
          refine ⟨16443199637237095705081121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 175394129463862354187531957 16443199637237095705081121)
          ·
            refine ⟨12332399727927821778810841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16443199637237095705081121 12332399727927821778810841)
            ·
              refine ⟨9249299795945866334108131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12332399727927821778810841 9249299795945866334108131)
              ·
                refine ⟨13873949693918799501162197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9249299795945866334108131 13873949693918799501162197)
                ·
                  refine ⟨325170695951221863308489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13873949693918799501162197 325170695951221863308489)
                  ·
                    rfl

theorem cell23_5699409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 1, 7].length) (baseStart_5699409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5699409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5699409 prefixEnd_5699409 := by exact prefixLift 5699409
  have htrace : WordTrace (prefixWord ++ tailWord_5699409) baseStart_5699409 baseEnd_5699409 := by
    simpa [prefixWord, tailWord_5699409, baseEnd_5699409] using wordTrace_append hprefix tailTrace_5699409
  have hstable : (prefixWord ++ tailWord_5699409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5699409).length < 2 ^ (prefixWord ++ tailWord_5699409).sum := by decide
  have hdescent : baseEnd_5699409 < baseStart_5699409 := by decide
  rcases family_descends (prefixWord ++ tailWord_5699409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5699420 : List Nat := [2, 2, 4, 2, 2, 2, 1, 1, 1, 4, 2]
def baseStart_5699420 : Nat := 118140960795 + 5699420 * 2 ^ 59
def prefixEnd_5699420 : Nat := 4983230072969 + 3 ^ 40 * 5699420 * 2
def baseEnd_5699420 : Nat := 2926541911848196226738851

theorem tailTrace_5699420 : CollatzResearch.WordTrace tailWord_5699420 prefixEnd_5699420 2926541911848196226738851 := by
  unfold tailWord_5699420
  simp only [CollatzResearch.WordTrace]
  refine ⟨103937462505991099143047857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138583283341321465524063809 103937462505991099143047857)
  ·
    refine ⟨77953096879493324357285893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103937462505991099143047857 77953096879493324357285893)
    ·
      refine ⟨14616205664904998316991105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77953096879493324357285893 14616205664904998316991105)
      ·
        refine ⟨10962154248678748737743329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14616205664904998316991105 10962154248678748737743329)
        ·
          refine ⟨8221615686509061553307497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10962154248678748737743329 8221615686509061553307497)
          ·
            refine ⟨6166211764881796164980623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8221615686509061553307497 6166211764881796164980623)
            ·
              refine ⟨9249317647322694247470935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6166211764881796164980623 9249317647322694247470935)
              ·
                refine ⟨13873976470984041371206403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9249317647322694247470935 13873976470984041371206403)
                ·
                  refine ⟨20810964706476062056809605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13873976470984041371206403 20810964706476062056809605)
                  ·
                    refine ⟨3902055882464261635651801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20810964706476062056809605 3902055882464261635651801)
                    ·
                      refine ⟨2926541911848196226738851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3902055882464261635651801 2926541911848196226738851)
                      ·
                        rfl

theorem cell23_5699420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_5699420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5699420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5699420 prefixEnd_5699420 := by exact prefixLift 5699420
  have htrace : WordTrace (prefixWord ++ tailWord_5699420) baseStart_5699420 baseEnd_5699420 := by
    simpa [prefixWord, tailWord_5699420, baseEnd_5699420] using wordTrace_append hprefix tailTrace_5699420
  have hstable : (prefixWord ++ tailWord_5699420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5699420).length < 2 ^ (prefixWord ++ tailWord_5699420).sum := by decide
  have hdescent : baseEnd_5699420 < baseStart_5699420 := by decide
  rcases family_descends (prefixWord ++ tailWord_5699420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5699459 : List Nat := [1, 1, 1, 3, 4, 2, 1, 1, 4, 1, 4]
def baseStart_5699459 : Nat := 118140960795 + 5699459 * 2 ^ 59
def prefixEnd_5699459 : Nat := 4983230072969 + 3 ^ 40 * 5699459 * 2
def baseEnd_5699459 : Nat := 2926561937593721574151171

theorem tailTrace_5699459 : CollatzResearch.WordTrace tailWord_5699459 prefixEnd_5699459 2926561937593721574151171 := by
  unfold tailWord_5699459
  simp only [CollatzResearch.WordTrace]
  refine ⟨207876347458840907946765431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138584231639227271964510287 207876347458840907946765431)
  ·
    refine ⟨311814521188261361920148147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207876347458840907946765431 311814521188261361920148147)
    ·
      refine ⟨467721781782392042880222221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311814521188261361920148147 467721781782392042880222221)
      ·
        refine ⟨175395668168397016080083333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 467721781782392042880222221 175395668168397016080083333)
        ·
          refine ⟨32886687781574440515015625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 175395668168397016080083333 32886687781574440515015625)
          ·
            refine ⟨24665015836180830386261719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32886687781574440515015625 24665015836180830386261719)
            ·
              refine ⟨36997523754271245579392579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24665015836180830386261719 36997523754271245579392579)
              ·
                refine ⟨55496285631406868369088869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36997523754271245579392579 55496285631406868369088869)
                ·
                  refine ⟨10405553555888787819204163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55496285631406868369088869 10405553555888787819204163)
                  ·
                    refine ⟨15608330333833181728806245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10405553555888787819204163 15608330333833181728806245)
                    ·
                      refine ⟨2926561937593721574151171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15608330333833181728806245 2926561937593721574151171)
                      ·
                        rfl

theorem cell23_5699459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 4, 1, 4].length) (baseStart_5699459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5699459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5699459 prefixEnd_5699459 := by exact prefixLift 5699459
  have htrace : WordTrace (prefixWord ++ tailWord_5699459) baseStart_5699459 baseEnd_5699459 := by
    simpa [prefixWord, tailWord_5699459, baseEnd_5699459] using wordTrace_append hprefix tailTrace_5699459
  have hstable : (prefixWord ++ tailWord_5699459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5699459).length < 2 ^ (prefixWord ++ tailWord_5699459).sum := by decide
  have hdescent : baseEnd_5699459 < baseStart_5699459 := by decide
  rcases family_descends (prefixWord ++ tailWord_5699459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5699466 : List Nat := [3, 1, 2, 4, 2, 1, 1, 1, 1, 2, 5]
def baseStart_5699466 : Nat := 118140960795 + 5699466 * 2 ^ 59
def prefixEnd_5699466 : Nat := 4983230072969 + 3 ^ 40 * 5699466 * 2
def baseEnd_5699466 : Nat := 2926565531958303046763639

theorem tailTrace_5699466 : CollatzResearch.WordTrace tailWord_5699466 prefixEnd_5699466 2926565531958303046763639 := by
  unfold tailWord_5699466
  simp only [CollatzResearch.WordTrace]
  refine ⟨51969150692453887035567563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138584401846543698761513501 51969150692453887035567563)
  ·
    refine ⟨77953726038680830553351345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51969150692453887035567563 77953726038680830553351345)
    ·
      refine ⟨58465294529010622915013509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77953726038680830553351345 58465294529010622915013509)
      ·
        refine ⟨10962242724189491796565033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58465294529010622915013509 10962242724189491796565033)
        ·
          refine ⟨8221682043142118847423775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10962242724189491796565033 8221682043142118847423775)
          ·
            refine ⟨12332523064713178271135663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8221682043142118847423775 12332523064713178271135663)
            ·
              refine ⟨18498784597069767406703495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12332523064713178271135663 18498784597069767406703495)
              ·
                refine ⟨27748176895604651110055243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18498784597069767406703495 27748176895604651110055243)
                ·
                  refine ⟨41622265343406976665082865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27748176895604651110055243 41622265343406976665082865)
                  ·
                    refine ⟨31216699007555232498812149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41622265343406976665082865 31216699007555232498812149)
                    ·
                      refine ⟨2926565531958303046763639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31216699007555232498812149 2926565531958303046763639)
                      ·
                        rfl

theorem cell23_5699466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_5699466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5699466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5699466 prefixEnd_5699466 := by exact prefixLift 5699466
  have htrace : WordTrace (prefixWord ++ tailWord_5699466) baseStart_5699466 baseEnd_5699466 := by
    simpa [prefixWord, tailWord_5699466, baseEnd_5699466] using wordTrace_append hprefix tailTrace_5699466
  have hstable : (prefixWord ++ tailWord_5699466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5699466).length < 2 ^ (prefixWord ++ tailWord_5699466).sum := by decide
  have hdescent : baseEnd_5699466 < baseStart_5699466 := by decide
  rcases family_descends (prefixWord ++ tailWord_5699466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5699472 : List Nat := [2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 6]
def baseStart_5699472 : Nat := 118140960795 + 5699472 * 2 ^ 59
def prefixEnd_5699472 : Nat := 4983230072969 + 3 ^ 40 * 5699472 * 2
def baseEnd_5699472 : Nat := 2926568612842230023288611

theorem tailTrace_5699472 : CollatzResearch.WordTrace tailWord_5699472 prefixEnd_5699472 2926568612842230023288611 := by
  unfold tailWord_5699472
  simp only [CollatzResearch.WordTrace]
  refine ⟨103938410803896905583494335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138584547738529207444659113 103938410803896905583494335)
  ·
    refine ⟨155907616205845358375241503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103938410803896905583494335 155907616205845358375241503)
    ·
      refine ⟨233861424308768037562862255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155907616205845358375241503 233861424308768037562862255)
      ·
        refine ⟨350792136463152056344293383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233861424308768037562862255 350792136463152056344293383)
        ·
          refine ⟨526188204694728084516440075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350792136463152056344293383 526188204694728084516440075)
          ·
            refine ⟨789282307042092126774660113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 526188204694728084516440075 789282307042092126774660113)
            ·
              refine ⟨591961730281569095080995085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 789282307042092126774660113 591961730281569095080995085)
              ·
                refine ⟨221985648855588410655373157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 591961730281569095080995085 221985648855588410655373157)
                ·
                  refine ⟨41622309160422826997882467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 221985648855588410655373157 41622309160422826997882467)
                  ·
                    refine ⟨62433463740634240496823701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41622309160422826997882467 62433463740634240496823701)
                    ·
                      refine ⟨2926568612842230023288611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62433463740634240496823701 2926568612842230023288611)
                      ·
                        rfl

theorem cell23_5699472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 6].length) (baseStart_5699472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5699472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5699472 prefixEnd_5699472 := by exact prefixLift 5699472
  have htrace : WordTrace (prefixWord ++ tailWord_5699472) baseStart_5699472 baseEnd_5699472 := by
    simpa [prefixWord, tailWord_5699472, baseEnd_5699472] using wordTrace_append hprefix tailTrace_5699472
  have hstable : (prefixWord ++ tailWord_5699472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5699472).length < 2 ^ (prefixWord ++ tailWord_5699472).sum := by decide
  have hdescent : baseEnd_5699472 < baseStart_5699472 := by decide
  rcases family_descends (prefixWord ++ tailWord_5699472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5699536 : List Nat := [2, 1, 1, 1, 1, 2, 4, 2, 4, 3, 2]
def baseStart_5699536 : Nat := 118140960795 + 5699536 * 2 ^ 59
def prefixEnd_5699536 : Nat := 4983230072969 + 3 ^ 40 * 5699536 * 2
def baseEnd_5699536 : Nat := 2926601475604117772888317

theorem tailTrace_5699536 : CollatzResearch.WordTrace tailWord_5699536 prefixEnd_5699536 2926601475604117772888317 := by
  unfold tailWord_5699536
  simp only [CollatzResearch.WordTrace]
  refine ⟨103939577939780975048659231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138586103919707966731545641 103939577939780975048659231)
  ·
    refine ⟨155909366909671462572988847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103939577939780975048659231 155909366909671462572988847)
    ·
      refine ⟨233864050364507193859483271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155909366909671462572988847 233864050364507193859483271)
      ·
        refine ⟨350796075546760790789224907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233864050364507193859483271 350796075546760790789224907)
        ·
          refine ⟨526194113320141186183837361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350796075546760790789224907 526194113320141186183837361)
          ·
            refine ⟨394645584990105889637878021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 526194113320141186183837361 394645584990105889637878021)
            ·
              refine ⟨73996047185644854307102129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 394645584990105889637878021 73996047185644854307102129)
              ·
                refine ⟨55497035389233640730326597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73996047185644854307102129 55497035389233640730326597)
                ·
                  refine ⟨10405694135481307636936237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55497035389233640730326597 10405694135481307636936237)
                  ·
                    refine ⟨3902135300805490363851089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10405694135481307636936237 3902135300805490363851089)
                    ·
                      refine ⟨2926601475604117772888317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3902135300805490363851089 2926601475604117772888317)
                      ·
                        rfl

theorem cell23_5699536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 4, 3, 2].length) (baseStart_5699536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5699536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5699536 prefixEnd_5699536 := by exact prefixLift 5699536
  have htrace : WordTrace (prefixWord ++ tailWord_5699536) baseStart_5699536 baseEnd_5699536 := by
    simpa [prefixWord, tailWord_5699536, baseEnd_5699536] using wordTrace_append hprefix tailTrace_5699536
  have hstable : (prefixWord ++ tailWord_5699536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5699536).length < 2 ^ (prefixWord ++ tailWord_5699536).sum := by decide
  have hdescent : baseEnd_5699536 < baseStart_5699536 := by decide
  rcases family_descends (prefixWord ++ tailWord_5699536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5699553 : List Nat := [1, 2, 3, 1, 2, 1, 5, 1, 2, 3, 2]
def baseStart_5699553 : Nat := 118140960795 + 5699553 * 2 ^ 59
def prefixEnd_5699553 : Nat := 4983230072969 + 3 ^ 40 * 5699553 * 2
def baseEnd_5699553 : Nat := 2926610204775244206375739

theorem tailTrace_5699553 : CollatzResearch.WordTrace tailWord_5699553 prefixEnd_5699553 2926610204775244206375739 := by
  unfold tailWord_5699553
  simp only [CollatzResearch.WordTrace]
  refine ⟨207879775920500362000687313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138586517280333574667124875 207879775920500362000687313)
  ·
    refine ⟨155909831940375271500515485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207879775920500362000687313 155909831940375271500515485)
    ·
      refine ⟨58466186977640726812693307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155909831940375271500515485 58466186977640726812693307)
      ·
        refine ⟨87699280466461090219039961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58466186977640726812693307 87699280466461090219039961)
        ·
          refine ⟨65774460349845817664279971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87699280466461090219039961 65774460349845817664279971)
          ·
            refine ⟨98661690524768726496419957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65774460349845817664279971 98661690524768726496419957)
            ·
              refine ⟨9249533486697068109039371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 98661690524768726496419957 9249533486697068109039371)
              ·
                refine ⟨13874300230045602163559057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9249533486697068109039371 13874300230045602163559057)
                ·
                  refine ⟨10405725172534201622669293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13874300230045602163559057 10405725172534201622669293)
                  ·
                    refine ⟨3902146939700325608500985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10405725172534201622669293 3902146939700325608500985)
                    ·
                      refine ⟨2926610204775244206375739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3902146939700325608500985 2926610204775244206375739)
                      ·
                        rfl

theorem cell23_5699553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 1, 2, 3, 2].length) (baseStart_5699553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5699553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5699553 prefixEnd_5699553 := by exact prefixLift 5699553
  have htrace : WordTrace (prefixWord ++ tailWord_5699553) baseStart_5699553 baseEnd_5699553 := by
    simpa [prefixWord, tailWord_5699553, baseEnd_5699553] using wordTrace_append hprefix tailTrace_5699553
  have hstable : (prefixWord ++ tailWord_5699553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5699553).length < 2 ^ (prefixWord ++ tailWord_5699553).sum := by decide
  have hdescent : baseEnd_5699553 < baseStart_5699553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5699553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5699579 : List Nat := [1, 1, 1, 1, 1, 3, 4, 2, 3, 2, 4]
def baseStart_5699579 : Nat := 118140960795 + 5699579 * 2 ^ 59
def prefixEnd_5699579 : Nat := 4983230072969 + 3 ^ 40 * 5699579 * 2
def baseEnd_5699579 : Nat := 2926623555272261104650619

theorem tailTrace_5699579 : CollatzResearch.WordTrace tailWord_5699579 prefixEnd_5699579 2926623555272261104650619 := by
  unfold tailWord_5699579
  simp only [CollatzResearch.WordTrace]
  refine ⟨207880724218406168441133791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138587149478937445627422527 207880724218406168441133791)
  ·
    refine ⟨311821086327609252661700687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207880724218406168441133791 311821086327609252661700687)
    ·
      refine ⟨467731629491413878992551031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311821086327609252661700687 467731629491413878992551031)
      ·
        refine ⟨701597444237120818488826547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 467731629491413878992551031 701597444237120818488826547)
        ·
          refine ⟨1052396166355681227733239821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 701597444237120818488826547 1052396166355681227733239821)
          ·
            refine ⟨394648562383380460399964933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1052396166355681227733239821 394648562383380460399964933)
            ·
              refine ⟨73996605446883836324993425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 394648562383380460399964933 73996605446883836324993425)
              ·
                refine ⟨55497454085162877243745069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73996605446883836324993425 55497454085162877243745069)
                ·
                  refine ⟨20811545281936078966404401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55497454085162877243745069 20811545281936078966404401)
                  ·
                    refine ⟨15608658961452059224803301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20811545281936078966404401 15608658961452059224803301)
                    ·
                      refine ⟨2926623555272261104650619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15608658961452059224803301 2926623555272261104650619)
                      ·
                        rfl

theorem cell23_5699579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3, 2, 4].length) (baseStart_5699579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5699579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5699579 prefixEnd_5699579 := by exact prefixLift 5699579
  have htrace : WordTrace (prefixWord ++ tailWord_5699579) baseStart_5699579 baseEnd_5699579 := by
    simpa [prefixWord, tailWord_5699579, baseEnd_5699579] using wordTrace_append hprefix tailTrace_5699579
  have hstable : (prefixWord ++ tailWord_5699579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5699579).length < 2 ^ (prefixWord ++ tailWord_5699579).sum := by decide
  have hdescent : baseEnd_5699579 < baseStart_5699579 := by decide
  rcases family_descends (prefixWord ++ tailWord_5699579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5699623 : List Nat := [1, 1, 7, 1, 2, 2, 9]
def baseStart_5699623 : Nat := 118140960795 + 5699623 * 2 ^ 59
def prefixEnd_5699623 : Nat := 4983230072969 + 3 ^ 40 * 5699623 * 2
def baseEnd_5699623 : Nat := 36131433931124184351857

theorem tailTrace_5699623 : CollatzResearch.WordTrace tailWord_5699623 prefixEnd_5699623 36131433931124184351857 := by
  unfold tailWord_5699623
  simp only [CollatzResearch.WordTrace]
  refine ⟨207882329030246763955735523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138588219353497842637157015 207882329030246763955735523)
  ·
    refine ⟨311823493545370145933603285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207882329030246763955735523 311823493545370145933603285)
    ·
      refine ⟨7308363129969612795318827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 311823493545370145933603285 7308363129969612795318827)
      ·
        refine ⟨10962544694954419192978241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7308363129969612795318827 10962544694954419192978241)
        ·
          refine ⟨8221908521215814394733681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10962544694954419192978241 8221908521215814394733681)
          ·
            refine ⟨6166431390911860796050261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8221908521215814394733681 6166431390911860796050261)
            ·
              refine ⟨36131433931124184351857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6166431390911860796050261 36131433931124184351857)
              ·
                rfl

theorem cell23_5699623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 9].length) (baseStart_5699623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5699623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5699623 prefixEnd_5699623 := by exact prefixLift 5699623
  have htrace : WordTrace (prefixWord ++ tailWord_5699623) baseStart_5699623 baseEnd_5699623 := by
    simpa [prefixWord, tailWord_5699623, baseEnd_5699623] using wordTrace_append hprefix tailTrace_5699623
  have hstable : (prefixWord ++ tailWord_5699623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5699623).length < 2 ^ (prefixWord ++ tailWord_5699623).sum := by decide
  have hdescent : baseEnd_5699623 < baseStart_5699623 := by decide
  rcases family_descends (prefixWord ++ tailWord_5699623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5699633 : List Nat := [1, 2, 2, 3, 1, 3, 2, 1, 4, 1, 3]
def baseStart_5699633 : Nat := 118140960795 + 5699633 * 2 ^ 59
def prefixEnd_5699633 : Nat := 4983230072969 + 3 ^ 40 * 5699633 * 2
def baseEnd_5699633 : Nat := 2926651283227603893375371

theorem tailTrace_5699633 : CollatzResearch.WordTrace tailWord_5699633 prefixEnd_5699633 2926651283227603893375371 := by
  unfold tailWord_5699633
  simp only [CollatzResearch.WordTrace]
  refine ⟨207882693760210535663599553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138588462506807023775733035 207882693760210535663599553)
  ·
    refine ⟨155912020320157901747699665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207882693760210535663599553 155912020320157901747699665)
    ·
      refine ⟨116934015240118426310774749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155912020320157901747699665 116934015240118426310774749)
      ·
        refine ⟨43850255715044409866540531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116934015240118426310774749 43850255715044409866540531)
        ·
          refine ⟨65775383572566614799810797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43850255715044409866540531 65775383572566614799810797)
          ·
            refine ⟨24665768839712480549929049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65775383572566614799810797 24665768839712480549929049)
            ·
              refine ⟨18499326629784360412446787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24665768839712480549929049 18499326629784360412446787)
              ·
                refine ⟨27748989944676540618670181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18499326629784360412446787 27748989944676540618670181)
                ·
                  refine ⟨5202935614626851366000659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27748989944676540618670181 5202935614626851366000659)
                  ·
                    refine ⟨7804403421940277049000989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5202935614626851366000659 7804403421940277049000989)
                    ·
                      refine ⟨2926651283227603893375371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7804403421940277049000989 2926651283227603893375371)
                      ·
                        rfl

theorem cell23_5699633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 4, 1, 3].length) (baseStart_5699633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5699633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5699633 prefixEnd_5699633 := by exact prefixLift 5699633
  have htrace : WordTrace (prefixWord ++ tailWord_5699633) baseStart_5699633 baseEnd_5699633 := by
    simpa [prefixWord, tailWord_5699633, baseEnd_5699633] using wordTrace_append hprefix tailTrace_5699633
  have hstable : (prefixWord ++ tailWord_5699633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5699633).length < 2 ^ (prefixWord ++ tailWord_5699633).sum := by decide
  have hdescent : baseEnd_5699633 < baseStart_5699633 := by decide
  rcases family_descends (prefixWord ++ tailWord_5699633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5699634 : List Nat := [3, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2]
def baseStart_5699634 : Nat := 118140960795 + 5699634 * 2 ^ 59
def prefixEnd_5699634 : Nat := 4983230072969 + 3 ^ 40 * 5699634 * 2
def baseEnd_5699634 : Nat := 2926651796708258389462867

theorem tailTrace_5699634 : CollatzResearch.WordTrace tailWord_5699634 prefixEnd_5699634 2926651796708258389462867 := by
  unfold tailWord_5699634
  simp only [CollatzResearch.WordTrace]
  refine ⟨51970682558301728208596489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138588486822137941889590637 51970682558301728208596489)
  ·
    refine ⟨38978011918726296156447367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51970682558301728208596489 38978011918726296156447367)
    ·
      refine ⟨58467017878089444234671051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38978011918726296156447367 58467017878089444234671051)
      ·
        refine ⟨87700526817134166352006577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58467017878089444234671051 87700526817134166352006577)
        ·
          refine ⟨65775395112850624764004933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87700526817134166352006577 65775395112850624764004933)
          ·
            refine ⟨12332886583659492143250925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65775395112850624764004933 12332886583659492143250925)
            ·
              refine ⟨4624832468872309553719097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12332886583659492143250925 4624832468872309553719097)
              ·
                refine ⟨3468624351654232165289323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4624832468872309553719097 3468624351654232165289323)
                ·
                  refine ⟨5202936527481348247933985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3468624351654232165289323 5202936527481348247933985)
                  ·
                    refine ⟨3902202395611011185950489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5202936527481348247933985 3902202395611011185950489)
                    ·
                      refine ⟨2926651796708258389462867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3902202395611011185950489 2926651796708258389462867)
                      ·
                        rfl

theorem cell23_5699634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2].length) (baseStart_5699634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5699634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5699634 prefixEnd_5699634 := by exact prefixLift 5699634
  have htrace : WordTrace (prefixWord ++ tailWord_5699634) baseStart_5699634 baseEnd_5699634 := by
    simpa [prefixWord, tailWord_5699634, baseEnd_5699634] using wordTrace_append hprefix tailTrace_5699634
  have hstable : (prefixWord ++ tailWord_5699634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5699634).length < 2 ^ (prefixWord ++ tailWord_5699634).sum := by decide
  have hdescent : baseEnd_5699634 < baseStart_5699634 := by decide
  rcases family_descends (prefixWord ++ tailWord_5699634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5699659 : List Nat := [1, 1, 1, 1, 3, 1, 2, 2, 3, 3, 5]
def baseStart_5699659 : Nat := 118140960795 + 5699659 * 2 ^ 59
def prefixEnd_5699659 : Nat := 4983230072969 + 3 ^ 40 * 5699659 * 2
def baseEnd_5699659 : Nat := 2926664633724620791650251

theorem tailTrace_5699659 : CollatzResearch.WordTrace tailWord_5699659 prefixEnd_5699659 2926664633724620791650251 := by
  unfold tailWord_5699659
  simp only [CollatzResearch.WordTrace]
  refine ⟨207883642058116342104046031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138589094705410894736030687 207883642058116342104046031)
  ·
    refine ⟨311825463087174513156069047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207883642058116342104046031 311825463087174513156069047)
    ·
      refine ⟨467738194630761769734103571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311825463087174513156069047 467738194630761769734103571)
      ·
        refine ⟨701607291946142654601155357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 467738194630761769734103571 701607291946142654601155357)
        ·
          refine ⟨263102734479803495475433259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 701607291946142654601155357 263102734479803495475433259)
          ·
            refine ⟨394654101719705243213149889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263102734479803495475433259 394654101719705243213149889)
            ·
              refine ⟨295990576289778932409862417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 394654101719705243213149889 295990576289778932409862417)
              ·
                refine ⟨221992932217334199307396813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 295990576289778932409862417 221992932217334199307396813)
                ·
                  refine ⟨83247349581500324740273805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 221992932217334199307396813 83247349581500324740273805)
                  ·
                    refine ⟨31217756093062621777602677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 83247349581500324740273805 31217756093062621777602677)
                    ·
                      refine ⟨2926664633724620791650251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31217756093062621777602677 2926664633724620791650251)
                      ·
                        rfl

theorem cell23_5699659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3, 5].length) (baseStart_5699659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5699659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5699659 prefixEnd_5699659 := by exact prefixLift 5699659
  have htrace : WordTrace (prefixWord ++ tailWord_5699659) baseStart_5699659 baseEnd_5699659 := by
    simpa [prefixWord, tailWord_5699659, baseEnd_5699659] using wordTrace_append hprefix tailTrace_5699659
  have hstable : (prefixWord ++ tailWord_5699659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5699659).length < 2 ^ (prefixWord ++ tailWord_5699659).sum := by decide
  have hdescent : baseEnd_5699659 < baseStart_5699659 := by decide
  rcases family_descends (prefixWord ++ tailWord_5699659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5699660 : List Nat := [2, 2, 1, 3, 1, 1, 5, 2, 1, 3, 2]
def baseStart_5699660 : Nat := 118140960795 + 5699660 * 2 ^ 59
def prefixEnd_5699660 : Nat := 4983230072969 + 3 ^ 40 * 5699660 * 2
def baseEnd_5699660 : Nat := 2926665147205275287737747

theorem tailTrace_5699660 : CollatzResearch.WordTrace tailWord_5699660 prefixEnd_5699660 2926665147205275287737747 := by
  unfold tailWord_5699660
  simp only [CollatzResearch.WordTrace]
  refine ⟨103941839265556359637416217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138589119020741812849888289 103941839265556359637416217)
  ·
    refine ⟨77956379449167269728062163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103941839265556359637416217 77956379449167269728062163)
    ·
      refine ⟨116934569173750904592093245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77956379449167269728062163 116934569173750904592093245)
      ·
        refine ⟨43850463440156589222034967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116934569173750904592093245 43850463440156589222034967)
        ·
          refine ⟨65775695160234883833052451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43850463440156589222034967 65775695160234883833052451)
          ·
            refine ⟨98663542740352325749578677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65775695160234883833052451 98663542740352325749578677)
            ·
              refine ⟨9249707131908030539023001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 98663542740352325749578677 9249707131908030539023001)
              ·
                refine ⟨6937280348931022904267251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9249707131908030539023001 6937280348931022904267251)
                ·
                  refine ⟨10405920523396534356400877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6937280348931022904267251 10405920523396534356400877)
                  ·
                    refine ⟨3902220196273700383650329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10405920523396534356400877 3902220196273700383650329)
                    ·
                      refine ⟨2926665147205275287737747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3902220196273700383650329 2926665147205275287737747)
                      ·
                        rfl

theorem cell23_5699660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 2, 1, 3, 2].length) (baseStart_5699660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5699660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5699660 prefixEnd_5699660 := by exact prefixLift 5699660
  have htrace : WordTrace (prefixWord ++ tailWord_5699660) baseStart_5699660 baseEnd_5699660 := by
    simpa [prefixWord, tailWord_5699660, baseEnd_5699660] using wordTrace_append hprefix tailTrace_5699660
  have hstable : (prefixWord ++ tailWord_5699660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5699660).length < 2 ^ (prefixWord ++ tailWord_5699660).sum := by decide
  have hdescent : baseEnd_5699660 < baseStart_5699660 := by decide
  rcases family_descends (prefixWord ++ tailWord_5699660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5699673 : List Nat := [1, 2, 1, 2, 2, 1, 5, 2, 1, 4, 2]
def baseStart_5699673 : Nat := 118140960795 + 5699673 * 2 ^ 59
def prefixEnd_5699673 : Nat := 4983230072969 + 3 ^ 40 * 5699673 * 2
def baseEnd_5699673 : Nat := 2926671822453783736875187

theorem tailTrace_5699673 : CollatzResearch.WordTrace tailWord_5699673 prefixEnd_5699673 2926671822453783736875187 := by
  unfold tailWord_5699673
  simp only [CollatzResearch.WordTrace]
  refine ⟨207884152680065622495055673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138589435120043748330037115 207884152680065622495055673)
  ·
    refine ⟨155913114510049216871291755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207884152680065622495055673 155913114510049216871291755)
    ·
      refine ⟨233869671765073825306937633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155913114510049216871291755 233869671765073825306937633)
      ·
        refine ⟨175402253823805368980203225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233869671765073825306937633 175402253823805368980203225)
        ·
          refine ⟨131551690367854026735152419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175402253823805368980203225 131551690367854026735152419)
          ·
            refine ⟨197327535551781040102728629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131551690367854026735152419 197327535551781040102728629)
            ·
              refine ⟨18499456457979472509630809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 197327535551781040102728629 18499456457979472509630809)
              ·
                refine ⟨13874592343484604382223107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18499456457979472509630809 13874592343484604382223107)
                ·
                  refine ⟨20811888515226906573334661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13874592343484604382223107 20811888515226906573334661)
                  ·
                    refine ⟨3902229096605044982500249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20811888515226906573334661 3902229096605044982500249)
                    ·
                      refine ⟨2926671822453783736875187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3902229096605044982500249 2926671822453783736875187)
                      ·
                        rfl

theorem cell23_5699673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2, 1, 4, 2].length) (baseStart_5699673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5699673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5699673 prefixEnd_5699673 := by exact prefixLift 5699673
  have htrace : WordTrace (prefixWord ++ tailWord_5699673) baseStart_5699673 baseEnd_5699673 := by
    simpa [prefixWord, tailWord_5699673, baseEnd_5699673] using wordTrace_append hprefix tailTrace_5699673
  have hstable : (prefixWord ++ tailWord_5699673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5699673).length < 2 ^ (prefixWord ++ tailWord_5699673).sum := by decide
  have hdescent : baseEnd_5699673 < baseStart_5699673 := by decide
  rcases family_descends (prefixWord ++ tailWord_5699673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5699679 : List Nat := [1, 1, 2, 3, 1, 1, 2, 1, 11]
def baseStart_5699679 : Nat := 118140960795 + 5699679 * 2 ^ 59
def prefixEnd_5699679 : Nat := 4983230072969 + 3 ^ 40 * 5699679 * 2
def baseEnd_5699679 : Nat := 325186100370856745933351

theorem tailTrace_5699679 : CollatzResearch.WordTrace tailWord_5699679 prefixEnd_5699679 325186100370856745933351 := by
  unfold tailWord_5699679
  simp only [CollatzResearch.WordTrace]
  refine ⟨207884371518043885519774091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138589581012029257013182727 207884371518043885519774091)
  ·
    refine ⟨311826557277065828279661137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207884371518043885519774091 311826557277065828279661137)
    ·
      refine ⟨233869917957799371209745853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311826557277065828279661137 233869917957799371209745853)
      ·
        refine ⟨87701219234174764203654695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 233869917957799371209745853 87701219234174764203654695)
        ·
          refine ⟨131551828851262146305482043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87701219234174764203654695 131551828851262146305482043)
          ·
            refine ⟨197327743276893219458223065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131551828851262146305482043 197327743276893219458223065)
            ·
              refine ⟨147995807457669914593667299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197327743276893219458223065 147995807457669914593667299)
              ·
                refine ⟨221993711186504871890500949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147995807457669914593667299 221993711186504871890500949)
                ·
                  refine ⟨325186100370856745933351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 221993711186504871890500949 325186100370856745933351)
                  ·
                    rfl

theorem cell23_5699679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 11].length) (baseStart_5699679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5699679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5699679 prefixEnd_5699679 := by exact prefixLift 5699679
  have htrace : WordTrace (prefixWord ++ tailWord_5699679) baseStart_5699679 baseEnd_5699679 := by
    simpa [prefixWord, tailWord_5699679, baseEnd_5699679] using wordTrace_append hprefix tailTrace_5699679
  have hstable : (prefixWord ++ tailWord_5699679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5699679).length < 2 ^ (prefixWord ++ tailWord_5699679).sum := by decide
  have hdescent : baseEnd_5699679 < baseStart_5699679 := by decide
  rcases family_descends (prefixWord ++ tailWord_5699679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5699713 : List Nat := [1, 2, 4, 2, 3, 1, 1, 2, 7]
def baseStart_5699713 : Nat := 118140960795 + 5699713 * 2 ^ 59
def prefixEnd_5699713 : Nat := 4983230072969 + 3 ^ 40 * 5699713 * 2
def baseEnd_5699713 : Nat := 325188040186662620041667

theorem tailTrace_5699713 : CollatzResearch.WordTrace tailWord_5699713 prefixEnd_5699713 325188040186662620041667 := by
  unfold tailWord_5699713
  simp only [CollatzResearch.WordTrace]
  refine ⟨207885611599920709326511793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138590407733280472884341195 207885611599920709326511793)
  ·
    refine ⟨155914208699940531994883845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207885611599920709326511793 155914208699940531994883845)
    ·
      refine ⟨29233914131238849749040721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 155914208699940531994883845 29233914131238849749040721)
      ·
        refine ⟨21925435598429137311780541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29233914131238849749040721 21925435598429137311780541)
        ·
          refine ⟨8222038349410926491917703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21925435598429137311780541 8222038349410926491917703)
          ·
            refine ⟨12333057524116389737876555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8222038349410926491917703 12333057524116389737876555)
            ·
              refine ⟨18499586286174584606814833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12333057524116389737876555 18499586286174584606814833)
              ·
                refine ⟨13874689714630938455111125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18499586286174584606814833 13874689714630938455111125)
                ·
                  refine ⟨325188040186662620041667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13874689714630938455111125 325188040186662620041667)
                  ·
                    rfl

theorem cell23_5699713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 2, 7].length) (baseStart_5699713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5699713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5699713 prefixEnd_5699713 := by exact prefixLift 5699713
  have htrace : WordTrace (prefixWord ++ tailWord_5699713) baseStart_5699713 baseEnd_5699713 := by
    simpa [prefixWord, tailWord_5699713, baseEnd_5699713] using wordTrace_append hprefix tailTrace_5699713
  have hstable : (prefixWord ++ tailWord_5699713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5699713).length < 2 ^ (prefixWord ++ tailWord_5699713).sum := by decide
  have hdescent : baseEnd_5699713 < baseStart_5699713 := by decide
  rcases family_descends (prefixWord ++ tailWord_5699713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5699730 : List Nat := [3, 2, 3, 1, 1, 1, 4, 3, 5]
def baseStart_5699730 : Nat := 118140960795 + 5699730 * 2 ^ 59
def prefixEnd_5699730 : Nat := 4983230072969 + 3 ^ 40 * 5699730 * 2
def baseEnd_5699730 : Nat := 325189010094565557095825

theorem tailTrace_5699730 : CollatzResearch.WordTrace tailWord_5699730 prefixEnd_5699730 325189010094565557095825 := by
  unfold tailWord_5699730
  simp only [CollatzResearch.WordTrace]
  refine ⟨51971557910214780307470161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138590821093906080819920429 51971557910214780307470161)
  ·
    refine ⟨38978668432661085230602621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51971557910214780307470161 38978668432661085230602621)
    ·
      refine ⟨14617000662247906961475983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38978668432661085230602621 14617000662247906961475983)
      ·
        refine ⟨21925500993371860442213975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14617000662247906961475983 21925500993371860442213975)
        ·
          refine ⟨32888251490057790663320963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21925500993371860442213975 32888251490057790663320963)
          ·
            refine ⟨49332377235086685994981445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32888251490057790663320963 49332377235086685994981445)
            ·
              refine ⟨9249820731578753624059021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49332377235086685994981445 9249820731578753624059021)
              ·
                refine ⟨3468682774342032609022133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9249820731578753624059021 3468682774342032609022133)
                ·
                  refine ⟨325189010094565557095825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3468682774342032609022133 325189010094565557095825)
                  ·
                    rfl

theorem cell23_5699730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 3, 5].length) (baseStart_5699730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5699730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5699730 prefixEnd_5699730 := by exact prefixLift 5699730
  have htrace : WordTrace (prefixWord ++ tailWord_5699730) baseStart_5699730 baseEnd_5699730 := by
    simpa [prefixWord, tailWord_5699730, baseEnd_5699730] using wordTrace_append hprefix tailTrace_5699730
  have hstable : (prefixWord ++ tailWord_5699730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5699730).length < 2 ^ (prefixWord ++ tailWord_5699730).sum := by decide
  have hdescent : baseEnd_5699730 < baseStart_5699730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5699730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5699758 : List Nat := [4, 1, 4, 2, 1, 1, 3, 1, 2, 2, 2]
def baseStart_5699758 : Nat := 118140960795 + 5699758 * 2 ^ 59
def prefixEnd_5699758 : Nat := 4983230072969 + 3 ^ 40 * 5699758 * 2
def baseEnd_5699758 : Nat := 2926715468309415904312297

theorem tailTrace_5699758 : CollatzResearch.WordTrace tailWord_5699758 prefixEnd_5699758 2926715468309415904312297 := by
  unfold tailWord_5699758
  simp only [CollatzResearch.WordTrace]
  refine ⟨25985906610594710251487491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138591501923171788007933285 25985906610594710251487491)
  ·
    refine ⟨38978859915892065377231237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25985906610594710251487491 38978859915892065377231237)
    ·
      refine ⟨7308536234229762258230857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38978859915892065377231237 7308536234229762258230857)
      ·
        refine ⟨5481402175672321693673143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7308536234229762258230857 5481402175672321693673143)
        ·
          refine ⟨8222103263508482540509715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5481402175672321693673143 8222103263508482540509715)
          ·
            refine ⟨12333154895262723810764573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8222103263508482540509715 12333154895262723810764573)
            ·
              refine ⟨4624933085723521429036715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12333154895262723810764573 4624933085723521429036715)
              ·
                refine ⟨6937399628585282143555073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4624933085723521429036715 6937399628585282143555073)
                ·
                  refine ⟨5203049721438961607666305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6937399628585282143555073 5203049721438961607666305)
                  ·
                    refine ⟨3902287291079221205749729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5203049721438961607666305 3902287291079221205749729)
                    ·
                      refine ⟨2926715468309415904312297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3902287291079221205749729 2926715468309415904312297)
                      ·
                        rfl

theorem cell23_5699758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_5699758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5699758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5699758 prefixEnd_5699758 := by exact prefixLift 5699758
  have htrace : WordTrace (prefixWord ++ tailWord_5699758) baseStart_5699758 baseEnd_5699758 := by
    simpa [prefixWord, tailWord_5699758, baseEnd_5699758] using wordTrace_append hprefix tailTrace_5699758
  have hstable : (prefixWord ++ tailWord_5699758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5699758).length < 2 ^ (prefixWord ++ tailWord_5699758).sum := by decide
  have hdescent : baseEnd_5699758 < baseStart_5699758 := by decide
  rcases family_descends (prefixWord ++ tailWord_5699758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5699786 : List Nat := [3, 1, 2, 1, 3, 1, 1, 1, 10]
def baseStart_5699786 : Nat := 118140960795 + 5699786 * 2 ^ 59
def prefixEnd_5699786 : Nat := 4983230072969 + 3 ^ 40 * 5699786 * 2
def baseEnd_5699786 : Nat := 325192205085304643862463

theorem tailTrace_5699786 : CollatzResearch.WordTrace tailWord_5699786 prefixEnd_5699786 325192205085304643862463 := by
  unfold tailWord_5699786
  simp only [CollatzResearch.WordTrace]
  refine ⟨51972068532164060698479803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138592182752437495195946141 51972068532164060698479803)
  ·
    refine ⟨77958102798246091047719705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51972068532164060698479803 77958102798246091047719705)
    ·
      refine ⟨58468577098684568285789779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77958102798246091047719705 58468577098684568285789779)
      ·
        refine ⟨87702865648026852428684669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58468577098684568285789779 87702865648026852428684669)
        ·
          refine ⟨32888574618010069660756751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87702865648026852428684669 32888574618010069660756751)
          ·
            refine ⟨49332861927015104491135127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32888574618010069660756751 49332861927015104491135127)
            ·
              refine ⟨73999292890522656736702691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49332861927015104491135127 73999292890522656736702691)
              ·
                refine ⟨110998939335783985105054037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73999292890522656736702691 110998939335783985105054037)
                ·
                  refine ⟨325192205085304643862463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 110998939335783985105054037 325192205085304643862463)
                  ·
                    rfl

theorem cell23_5699786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 10].length) (baseStart_5699786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5699786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5699786 prefixEnd_5699786 := by exact prefixLift 5699786
  have htrace : WordTrace (prefixWord ++ tailWord_5699786) baseStart_5699786 baseEnd_5699786 := by
    simpa [prefixWord, tailWord_5699786, baseEnd_5699786] using wordTrace_append hprefix tailTrace_5699786
  have hstable : (prefixWord ++ tailWord_5699786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5699786).length < 2 ^ (prefixWord ++ tailWord_5699786).sum := by decide
  have hdescent : baseEnd_5699786 < baseStart_5699786 := by decide
  rcases family_descends (prefixWord ++ tailWord_5699786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5699800 : List Nat := [2, 1, 2, 2, 4, 2, 1, 2, 2, 2, 3]
def baseStart_5699800 : Nat := 118140960795 + 5699800 * 2 ^ 59
def prefixEnd_5699800 : Nat := 4983230072969 + 3 ^ 40 * 5699800 * 2
def baseEnd_5699800 : Nat := 2926737034496904739987103

theorem tailTrace_5699800 : CollatzResearch.WordTrace tailWord_5699800 prefixEnd_5699800 2926737034496904739987103 := by
  unfold tailWord_5699800
  simp only [CollatzResearch.WordTrace]
  refine ⟨103944392375302761592464427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138592523167070348789952569 103944392375302761592464427)
  ·
    refine ⟨155916588562954142388696641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103944392375302761592464427 155916588562954142388696641)
    ·
      refine ⟨116937441422215606791522481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155916588562954142388696641 116937441422215606791522481)
      ·
        refine ⟨87703081066661705093641861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116937441422215606791522481 87703081066661705093641861)
        ·
          refine ⟨16444327699999069705057849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87703081066661705093641861 16444327699999069705057849)
          ·
            refine ⟨12333245774999302278793387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16444327699999069705057849 12333245774999302278793387)
            ·
              refine ⟨18499868662498953418190081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12333245774999302278793387 18499868662498953418190081)
              ·
                refine ⟨13874901496874215063642561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18499868662498953418190081 13874901496874215063642561)
                ·
                  refine ⟨10406176122655661297731921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13874901496874215063642561 10406176122655661297731921)
                  ·
                    refine ⟨7804632091991745973298941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10406176122655661297731921 7804632091991745973298941)
                    ·
                      refine ⟨2926737034496904739987103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7804632091991745973298941 2926737034496904739987103)
                      ·
                        rfl

theorem cell23_5699800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 2, 2, 2, 3].length) (baseStart_5699800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5699800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5699800 prefixEnd_5699800 := by exact prefixLift 5699800
  have htrace : WordTrace (prefixWord ++ tailWord_5699800) baseStart_5699800 baseEnd_5699800 := by
    simpa [prefixWord, tailWord_5699800, baseEnd_5699800] using wordTrace_append hprefix tailTrace_5699800
  have hstable : (prefixWord ++ tailWord_5699800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5699800).length < 2 ^ (prefixWord ++ tailWord_5699800).sum := by decide
  have hdescent : baseEnd_5699800 < baseStart_5699800 := by decide
  rcases family_descends (prefixWord ++ tailWord_5699800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5699833 : List Nat := [1, 2, 1, 3, 1, 1, 2, 6, 1, 5]
def baseStart_5699833 : Nat := 118140960795 + 5699833 * 2 ^ 59
def prefixEnd_5699833 : Nat := 4983230072969 + 3 ^ 40 * 5699833 * 2
def baseEnd_5699833 : Nat := 975584659786167703624817

theorem tailTrace_5699833 : CollatzResearch.WordTrace tailWord_5699833 prefixEnd_5699833 975584659786167703624817 := by
  unfold tailWord_5699833
  simp only [CollatzResearch.WordTrace]
  refine ⟨207889988359485969820880153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138593325572990646547253435 207889988359485969820880153)
  ·
    refine ⟨155917491269614477365660115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207889988359485969820880153 155917491269614477365660115)
    ·
      refine ⟨233876236904421716048490173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155917491269614477365660115 233876236904421716048490173)
      ·
        refine ⟨87703588839158143518183815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 233876236904421716048490173 87703588839158143518183815)
        ·
          refine ⟨131555383258737215277275723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87703588839158143518183815 131555383258737215277275723)
          ·
            refine ⟨197333074888105822915913585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131555383258737215277275723 197333074888105822915913585)
            ·
              refine ⟨147999806166079367186935189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197333074888105822915913585 147999806166079367186935189)
              ·
                refine ⟨6937490914034970336887587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 147999806166079367186935189 6937490914034970336887587)
                ·
                  refine ⟨10406236371052455505331381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6937490914034970336887587 10406236371052455505331381)
                  ·
                    refine ⟨975584659786167703624817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10406236371052455505331381 975584659786167703624817)
                    ·
                      rfl

theorem cell23_5699833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 6, 1, 5].length) (baseStart_5699833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5699833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5699833 prefixEnd_5699833 := by exact prefixLift 5699833
  have htrace : WordTrace (prefixWord ++ tailWord_5699833) baseStart_5699833 baseEnd_5699833 := by
    simpa [prefixWord, tailWord_5699833, baseEnd_5699833] using wordTrace_append hprefix tailTrace_5699833
  have hstable : (prefixWord ++ tailWord_5699833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5699833).length < 2 ^ (prefixWord ++ tailWord_5699833).sum := by decide
  have hdescent : baseEnd_5699833 < baseStart_5699833 := by decide
  rcases family_descends (prefixWord ++ tailWord_5699833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5699840 : List Nat := [2, 1, 1, 2, 1, 1, 5, 3, 2, 3, 2]
def baseStart_5699840 : Nat := 118140960795 + 5699840 * 2 ^ 59
def prefixEnd_5699840 : Nat := 4983230072969 + 3 ^ 40 * 5699840 * 2
def baseEnd_5699840 : Nat := 2926757573723084583486919

theorem tailTrace_5699840 : CollatzResearch.WordTrace tailWord_5699840 prefixEnd_5699840 2926757573723084583486919 := by
  unfold tailWord_5699840
  simp only [CollatzResearch.WordTrace]
  refine ⟨103945121835230305008192487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138593495780307073344256649 103945121835230305008192487)
  ·
    refine ⟨155917682752845457512288731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103945121835230305008192487 155917682752845457512288731)
    ·
      refine ⟨233876524129268186268433097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155917682752845457512288731 233876524129268186268433097)
      ·
        refine ⟨175407393096951139701324823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233876524129268186268433097 175407393096951139701324823)
        ·
          refine ⟨263111089645426709551987235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175407393096951139701324823 263111089645426709551987235)
          ·
            refine ⟨394666634468140064327980853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263111089645426709551987235 394666634468140064327980853)
            ·
              refine ⟨36999996981388131030748205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 394666634468140064327980853 36999996981388131030748205)
              ·
                refine ⟨13874998868020549136530577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36999996981388131030748205 13874998868020549136530577)
                ·
                  refine ⟨10406249151015411852397933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13874998868020549136530577 10406249151015411852397933)
                  ·
                    refine ⟨3902343431630779444649225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10406249151015411852397933 3902343431630779444649225)
                    ·
                      refine ⟨2926757573723084583486919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3902343431630779444649225 2926757573723084583486919)
                      ·
                        rfl

theorem cell23_5699840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3, 2, 3, 2].length) (baseStart_5699840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5699840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5699840 prefixEnd_5699840 := by exact prefixLift 5699840
  have htrace : WordTrace (prefixWord ++ tailWord_5699840) baseStart_5699840 baseEnd_5699840 := by
    simpa [prefixWord, tailWord_5699840, baseEnd_5699840] using wordTrace_append hprefix tailTrace_5699840
  have hstable : (prefixWord ++ tailWord_5699840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5699840).length < 2 ^ (prefixWord ++ tailWord_5699840).sum := by decide
  have hdescent : baseEnd_5699840 < baseStart_5699840 := by decide
  rcases family_descends (prefixWord ++ tailWord_5699840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5699873 : List Nat := [1, 2, 3, 2, 1, 1, 2, 4, 1, 1, 5]
def baseStart_5699873 : Nat := 118140960795 + 5699873 * 2 ^ 59
def prefixEnd_5699873 : Nat := 4983230072969 + 3 ^ 40 * 5699873 * 2
def baseEnd_5699873 : Nat := 2926774518584682954374267

theorem tailTrace_5699873 : CollatzResearch.WordTrace tailWord_5699873 prefixEnd_5699873 2926774518584682954374267 := by
  unfold tailWord_5699873
  simp only [CollatzResearch.WordTrace]
  refine ⟨207891447279341056652336273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138594298186227371101557515 207891447279341056652336273)
  ·
    refine ⟨155918585459505792489252205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207891447279341056652336273 155918585459505792489252205)
    ·
      refine ⟨58469469547314672183469577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155918585459505792489252205 58469469547314672183469577)
      ·
        refine ⟨43852102160486004137602183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58469469547314672183469577 43852102160486004137602183)
        ·
          refine ⟨65778153240729006206403275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43852102160486004137602183 65778153240729006206403275)
          ·
            refine ⟨98667229861093509309604913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65778153240729006206403275 98667229861093509309604913)
            ·
              refine ⟨74000422395820131982203685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98667229861093509309604913 74000422395820131982203685)
              ·
                refine ⟨13875079199216274746663191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74000422395820131982203685 13875079199216274746663191)
                ·
                  refine ⟨20812618798824412119994787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13875079199216274746663191 20812618798824412119994787)
                  ·
                    refine ⟨31218928198236618179992181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20812618798824412119994787 31218928198236618179992181)
                    ·
                      refine ⟨2926774518584682954374267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31218928198236618179992181 2926774518584682954374267)
                      ·
                        rfl

theorem cell23_5699873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_5699873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5699873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5699873 prefixEnd_5699873 := by exact prefixLift 5699873
  have htrace : WordTrace (prefixWord ++ tailWord_5699873) baseStart_5699873 baseEnd_5699873 := by
    simpa [prefixWord, tailWord_5699873, baseEnd_5699873] using wordTrace_append hprefix tailTrace_5699873
  have hstable : (prefixWord ++ tailWord_5699873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5699873).length < 2 ^ (prefixWord ++ tailWord_5699873).sum := by decide
  have hdescent : baseEnd_5699873 < baseStart_5699873 := by decide
  rcases family_descends (prefixWord ++ tailWord_5699873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5699907 : List Nat := [1, 1, 1, 3, 1, 3, 6, 1, 1, 2, 3]
def baseStart_5699907 : Nat := 118140960795 + 5699907 * 2 ^ 59
def prefixEnd_5699907 : Nat := 4983230072969 + 3 ^ 40 * 5699907 * 2
def baseEnd_5699907 : Nat := 2926791976926935821349111

theorem tailTrace_5699907 : CollatzResearch.WordTrace tailWord_5699907 prefixEnd_5699907 2926791976926935821349111 := by
  unfold tailWord_5699907
  simp only [CollatzResearch.WordTrace]
  refine ⟨207892687361217880459073975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138595124907478586972715983 207892687361217880459073975)
  ·
    refine ⟨311839031041826820688610963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207892687361217880459073975 311839031041826820688610963)
    ·
      refine ⟨467758546562740231032916445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311839031041826820688610963 467758546562740231032916445)
      ·
        refine ⟨175409454961027586637343667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 467758546562740231032916445 175409454961027586637343667)
        ·
          refine ⟨263114182441541379956015501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175409454961027586637343667 263114182441541379956015501)
          ·
            refine ⟨98667818415578017483505813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 263114182441541379956015501 98667818415578017483505813)
            ·
              refine ⟨4625053988230219569539335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 98667818415578017483505813 4625053988230219569539335)
              ·
                refine ⟨6937580982345329354309003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4625053988230219569539335 6937580982345329354309003)
                ·
                  refine ⟨10406371473517994031463505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6937580982345329354309003 10406371473517994031463505)
                  ·
                    refine ⟨7804778605138495523597629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10406371473517994031463505 7804778605138495523597629)
                    ·
                      refine ⟨2926791976926935821349111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7804778605138495523597629 2926791976926935821349111)
                      ·
                        rfl

theorem cell23_5699907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 1, 1, 2, 3].length) (baseStart_5699907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5699907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5699907 prefixEnd_5699907 := by exact prefixLift 5699907
  have htrace : WordTrace (prefixWord ++ tailWord_5699907) baseStart_5699907 baseEnd_5699907 := by
    simpa [prefixWord, tailWord_5699907, baseEnd_5699907] using wordTrace_append hprefix tailTrace_5699907
  have hstable : (prefixWord ++ tailWord_5699907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5699907).length < 2 ^ (prefixWord ++ tailWord_5699907).sum := by decide
  have hdescent : baseEnd_5699907 < baseStart_5699907 := by decide
  rcases family_descends (prefixWord ++ tailWord_5699907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5699963 : List Nat := [1, 1, 1, 1, 1, 7, 1, 1, 1, 3, 5]
def baseStart_5699963 : Nat := 118140960795 + 5699963 * 2 ^ 59
def prefixEnd_5699963 : Nat := 4983230072969 + 3 ^ 40 * 5699963 * 2
def baseEnd_5699963 : Nat := 2926820731843587602248853

theorem tailTrace_5699963 : CollatzResearch.WordTrace tailWord_5699963 prefixEnd_5699963 2926820731843587602248853 := by
  unfold tailWord_5699963
  simp only [CollatzResearch.WordTrace]
  refine ⟨207894729849015002023112543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138596486566010001348741695 207894729849015002023112543)
  ·
    refine ⟨311842094773522503034668815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207894729849015002023112543 311842094773522503034668815)
    ·
      refine ⟨467763142160283754552003223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311842094773522503034668815 467763142160283754552003223)
      ·
        refine ⟨701644713240425631828004835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 467763142160283754552003223 701644713240425631828004835)
        ·
          refine ⟨1052467069860638447742007253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 701644713240425631828004835 1052467069860638447742007253)
          ·
            refine ⟨24667196949858713618953295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1052467069860638447742007253 24667196949858713618953295)
            ·
              refine ⟨37000795424788070428429943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24667196949858713618953295 37000795424788070428429943)
              ·
                refine ⟨55501193137182105642644915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37000795424788070428429943 55501193137182105642644915)
                ·
                  refine ⟨83251789705773158463967373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55501193137182105642644915 83251789705773158463967373)
                  ·
                    refine ⟨31219421139664934423987765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 83251789705773158463967373 31219421139664934423987765)
                    ·
                      refine ⟨2926820731843587602248853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31219421139664934423987765 2926820731843587602248853)
                      ·
                        rfl

theorem cell23_5699963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 3, 5].length) (baseStart_5699963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5699963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5699963 prefixEnd_5699963 := by exact prefixLift 5699963
  have htrace : WordTrace (prefixWord ++ tailWord_5699963) baseStart_5699963 baseEnd_5699963 := by
    simpa [prefixWord, tailWord_5699963, baseEnd_5699963] using wordTrace_append hprefix tailTrace_5699963
  have hstable : (prefixWord ++ tailWord_5699963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5699963).length < 2 ^ (prefixWord ++ tailWord_5699963).sum := by decide
  have hdescent : baseEnd_5699963 < baseStart_5699963 := by decide
  rcases family_descends (prefixWord ++ tailWord_5699963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5699988 : List Nat := [2, 4, 2, 1, 3, 2, 2, 1, 2, 1, 3]
def baseStart_5699988 : Nat := 118140960795 + 5699988 * 2 ^ 59
def prefixEnd_5699988 : Nat := 4983230072969 + 3 ^ 40 * 5699988 * 2
def baseEnd_5699988 : Nat := 2926833568859950004436239

theorem tailTrace_5699988 : CollatzResearch.WordTrace tailWord_5699988 prefixEnd_5699988 2926833568859950004436239 := by
  unfold tailWord_5699988
  simp only [CollatzResearch.WordTrace]
  refine ⟨103947820836962215646386309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138597094449282954195181745 103947820836962215646386309)
  ·
    refine ⟨19490216406930415433697433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103947820836962215646386309 19490216406930415433697433)
    ·
      refine ⟨14617662305197811575273075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19490216406930415433697433 14617662305197811575273075)
      ·
        refine ⟨21926493457796717362909613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14617662305197811575273075 21926493457796717362909613)
        ·
          refine ⟨8222435046673769011091105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21926493457796717362909613 8222435046673769011091105)
          ·
            refine ⟨6166826285005326758318329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8222435046673769011091105 6166826285005326758318329)
            ·
              refine ⟨4625119713753995068738747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6166826285005326758318329 4625119713753995068738747)
              ·
                refine ⟨6937679570630992603108121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4625119713753995068738747 6937679570630992603108121)
                ·
                  refine ⟨5203259677973244452331091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6937679570630992603108121 5203259677973244452331091)
                  ·
                    refine ⟨7804889516959866678496637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5203259677973244452331091 7804889516959866678496637)
                    ·
                      refine ⟨2926833568859950004436239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7804889516959866678496637 2926833568859950004436239)
                      ·
                        rfl

theorem cell23_5699988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_5699988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5699988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5699988 prefixEnd_5699988 := by exact prefixLift 5699988
  have htrace : WordTrace (prefixWord ++ tailWord_5699988) baseStart_5699988 baseEnd_5699988 := by
    simpa [prefixWord, tailWord_5699988, baseEnd_5699988] using wordTrace_append hprefix tailTrace_5699988
  have hstable : (prefixWord ++ tailWord_5699988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5699988).length < 2 ^ (prefixWord ++ tailWord_5699988).sum := by decide
  have hdescent : baseEnd_5699988 < baseStart_5699988 := by decide
  rcases family_descends (prefixWord ++ tailWord_5699988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5699998 : List Nat := [4, 3, 1, 2, 1, 3, 1, 2, 1, 3, 2]
def baseStart_5699998 : Nat := 118140960795 + 5699998 * 2 ^ 59
def prefixEnd_5699998 : Nat := 4983230072969 + 3 ^ 40 * 5699998 * 2
def baseEnd_5699998 : Nat := 2926838703666494965311193

theorem tailTrace_5699998 : CollatzResearch.WordTrace tailWord_5699998 prefixEnd_5699998 2926838703666494965311193 := by
  unfold tailWord_5699998
  simp only [CollatzResearch.WordTrace]
  refine ⟨25987000800486025375079581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138597337602592135333757765 25987000800486025375079581)
  ·
    refine ⟨9745125300182259515654843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25987000800486025375079581 9745125300182259515654843)
    ·
      refine ⟨14617687950273389273482265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9745125300182259515654843 14617687950273389273482265)
      ·
        refine ⟨10963265962705041955111699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14617687950273389273482265 10963265962705041955111699)
        ·
          refine ⟨16444898944057562932667549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10963265962705041955111699 16444898944057562932667549)
          ·
            refine ⟨6166837104021586099750331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16444898944057562932667549 6166837104021586099750331)
            ·
              refine ⟨9250255656032379149625497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6166837104021586099750331 9250255656032379149625497)
              ·
                refine ⟨6937691742024284362219123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9250255656032379149625497 6937691742024284362219123)
                ·
                  refine ⟨10406537613036426543328685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6937691742024284362219123 10406537613036426543328685)
                  ·
                    refine ⟨3902451604888659953748257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10406537613036426543328685 3902451604888659953748257)
                    ·
                      refine ⟨2926838703666494965311193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3902451604888659953748257 2926838703666494965311193)
                      ·
                        rfl

theorem cell23_5699998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_5699998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5699998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5699998 prefixEnd_5699998 := by exact prefixLift 5699998
  have htrace : WordTrace (prefixWord ++ tailWord_5699998) baseStart_5699998 baseEnd_5699998 := by
    simpa [prefixWord, tailWord_5699998, baseEnd_5699998] using wordTrace_append hprefix tailTrace_5699998
  have hstable : (prefixWord ++ tailWord_5699998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5699998).length < 2 ^ (prefixWord ++ tailWord_5699998).sum := by decide
  have hdescent : baseEnd_5699998 < baseStart_5699998 := by decide
  rcases family_descends (prefixWord ++ tailWord_5699998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5700040 : List Nat := [2, 1, 3, 1, 3, 2, 2, 1, 1, 2, 5]
def baseStart_5700040 : Nat := 118140960795 + 5700040 * 2 ^ 59
def prefixEnd_5700040 : Nat := 4983230072969 + 3 ^ 40 * 5700040 * 2
def baseEnd_5700040 : Nat := 2926860269853983800985999

theorem tailTrace_5700040 : CollatzResearch.WordTrace tailWord_5700040 prefixEnd_5700040 2926860269853983800985999 := by
  unfold tailWord_5700040
  simp only [CollatzResearch.WordTrace]
  refine ⟨103948769134868022086832787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138598358846490696115777049 103948769134868022086832787)
  ·
    refine ⟨155923153702302033130249181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103948769134868022086832787 155923153702302033130249181)
    ·
      refine ⟨58471182638363262423843443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155923153702302033130249181 58471182638363262423843443)
      ·
        refine ⟨87706773957544893635765165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58471182638363262423843443 87706773957544893635765165)
        ·
          refine ⟨32890040234079335113411937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87706773957544893635765165 32890040234079335113411937)
          ·
            refine ⟨24667530175559501335058953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32890040234079335113411937 24667530175559501335058953)
            ·
              refine ⟨18500647631669626001294215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24667530175559501335058953 18500647631669626001294215)
              ·
                refine ⟨27750971447504439001941323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18500647631669626001294215 27750971447504439001941323)
                ·
                  refine ⟨41626457171256658502911985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27750971447504439001941323 41626457171256658502911985)
                  ·
                    refine ⟨31219842878442493877183989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41626457171256658502911985 31219842878442493877183989)
                    ·
                      refine ⟨2926860269853983800985999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31219842878442493877183989 2926860269853983800985999)
                      ·
                        rfl

theorem cell23_5700040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_5700040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5700040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5700040 prefixEnd_5700040 := by exact prefixLift 5700040
  have htrace : WordTrace (prefixWord ++ tailWord_5700040) baseStart_5700040 baseEnd_5700040 := by
    simpa [prefixWord, tailWord_5700040, baseEnd_5700040] using wordTrace_append hprefix tailTrace_5700040
  have hstable : (prefixWord ++ tailWord_5700040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5700040).length < 2 ^ (prefixWord ++ tailWord_5700040).sum := by decide
  have hdescent : baseEnd_5700040 < baseStart_5700040 := by decide
  rcases family_descends (prefixWord ++ tailWord_5700040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5700043 : List Nat := [1, 1, 1, 1, 3, 3, 1, 2, 2, 8]
def baseStart_5700043 : Nat := 118140960795 + 5700043 * 2 ^ 59
def prefixEnd_5700043 : Nat := 4983230072969 + 3 ^ 40 * 5700043 * 2
def baseEnd_5700043 : Nat := 975620603431982429749495

theorem tailTrace_5700043 : CollatzResearch.WordTrace tailWord_5700043 prefixEnd_5700043 975620603431982429749495 := by
  unfold tailWord_5700043
  simp only [CollatzResearch.WordTrace]
  refine ⟨207897647688725175686024783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138598431792483450457349855 207897647688725175686024783)
  ·
    refine ⟨311846471533087763529037175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207897647688725175686024783 311846471533087763529037175)
    ·
      refine ⟨467769707299631645293555763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311846471533087763529037175 467769707299631645293555763)
      ·
        refine ⟨701654560949447467940333645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 467769707299631645293555763 701654560949447467940333645)
        ·
          refine ⟨263120460356042800477625117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 701654560949447467940333645 263120460356042800477625117)
          ·
            refine ⟨98670172633516050179109419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 263120460356042800477625117 98670172633516050179109419)
            ·
              refine ⟨148005258950274075268664129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98670172633516050179109419 148005258950274075268664129)
              ·
                refine ⟨111003944212705556451498097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148005258950274075268664129 111003944212705556451498097)
                ·
                  refine ⟨83252958159529167338623573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111003944212705556451498097 83252958159529167338623573)
                  ·
                    refine ⟨975620603431982429749495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 83252958159529167338623573 975620603431982429749495)
                    ·
                      rfl

theorem cell23_5700043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 8].length) (baseStart_5700043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5700043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5700043 prefixEnd_5700043 := by exact prefixLift 5700043
  have htrace : WordTrace (prefixWord ++ tailWord_5700043) baseStart_5700043 baseEnd_5700043 := by
    simpa [prefixWord, tailWord_5700043, baseEnd_5700043] using wordTrace_append hprefix tailTrace_5700043
  have hstable : (prefixWord ++ tailWord_5700043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5700043).length < 2 ^ (prefixWord ++ tailWord_5700043).sum := by decide
  have hdescent : baseEnd_5700043 < baseStart_5700043 := by decide
  rcases family_descends (prefixWord ++ tailWord_5700043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5700054 : List Nat := [5, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2]
def baseStart_5700054 : Nat := 118140960795 + 5700054 * 2 ^ 59
def prefixEnd_5700054 : Nat := 4983230072969 + 3 ^ 40 * 5700054 * 2
def baseEnd_5700054 : Nat := 2926867458583146746210935

theorem tailTrace_5700054 : CollatzResearch.WordTrace tailWord_5700054 prefixEnd_5700054 2926867458583146746210935 := by
  unfold tailWord_5700054
  simp only [CollatzResearch.WordTrace]
  refine ⟨12993628055730332785292201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 138598699261123549709783477 12993628055730332785292201)
  ·
    refine ⟨9745221041797749588969151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12993628055730332785292201 9745221041797749588969151)
    ·
      refine ⟨14617831562696624383453727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9745221041797749588969151 14617831562696624383453727)
      ·
        refine ⟨21926747344044936575180591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14617831562696624383453727 21926747344044936575180591)
        ·
          refine ⟨32890121016067404862770887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21926747344044936575180591 32890121016067404862770887)
          ·
            refine ⟨49335181524101107294156331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32890121016067404862770887 49335181524101107294156331)
            ·
              refine ⟨74002772286151660941234497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49335181524101107294156331 74002772286151660941234497)
              ·
                refine ⟨55502079214613745705925873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74002772286151660941234497 55502079214613745705925873)
                ·
                  refine ⟨41626559410960309279444405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55502079214613745705925873 41626559410960309279444405)
                  ·
                    refine ⟨3902489944777528994947913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41626559410960309279444405 3902489944777528994947913)
                    ·
                      refine ⟨2926867458583146746210935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3902489944777528994947913 2926867458583146746210935)
                      ·
                        rfl

theorem cell23_5700054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_5700054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5700054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5700054 prefixEnd_5700054 := by exact prefixLift 5700054
  have htrace : WordTrace (prefixWord ++ tailWord_5700054) baseStart_5700054 baseEnd_5700054 := by
    simpa [prefixWord, tailWord_5700054, baseEnd_5700054] using wordTrace_append hprefix tailTrace_5700054
  have hstable : (prefixWord ++ tailWord_5700054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5700054).length < 2 ^ (prefixWord ++ tailWord_5700054).sum := by decide
  have hdescent : baseEnd_5700054 < baseStart_5700054 := by decide
  rcases family_descends (prefixWord ++ tailWord_5700054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5700067 : List Nat := [1, 1, 1, 6, 3, 1, 1, 1, 1, 3, 4]
def baseStart_5700067 : Nat := 118140960795 + 5700067 * 2 ^ 59
def prefixEnd_5700067 : Nat := 4983230072969 + 3 ^ 40 * 5700067 * 2
def baseEnd_5700067 : Nat := 2926874133831655195348375

theorem tailTrace_5700067 : CollatzResearch.WordTrace tailWord_5700067 prefixEnd_5700067 2926874133831655195348375 := by
  unfold tailWord_5700067
  simp only [CollatzResearch.WordTrace]
  refine ⟨207898523040638227784898455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138599015360425485189932303 207898523040638227784898455)
  ·
    refine ⟨311847784560957341677347683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207898523040638227784898455 311847784560957341677347683)
    ·
      refine ⟨467771676841436012516021525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311847784560957341677347683 467771676841436012516021525)
      ·
        refine ⟨21926797351942313086688509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 467771676841436012516021525 21926797351942313086688509)
        ·
          refine ⟨8222549006978367407508191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21926797351942313086688509 8222549006978367407508191)
          ·
            refine ⟨12333823510467551111262287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8222549006978367407508191 12333823510467551111262287)
            ·
              refine ⟨18500735265701326666893431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12333823510467551111262287 18500735265701326666893431)
              ·
                refine ⟨27751102898551990000340147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18500735265701326666893431 27751102898551990000340147)
                ·
                  refine ⟨41626654347827985000510221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27751102898551990000340147 41626654347827985000510221)
                  ·
                    refine ⟨15609995380435494375191333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41626654347827985000510221 15609995380435494375191333)
                    ·
                      refine ⟨2926874133831655195348375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15609995380435494375191333 2926874133831655195348375)
                      ·
                        rfl

theorem cell23_5700067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_5700067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5700067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5700067 prefixEnd_5700067 := by exact prefixLift 5700067
  have htrace : WordTrace (prefixWord ++ tailWord_5700067) baseStart_5700067 baseEnd_5700067 := by
    simpa [prefixWord, tailWord_5700067, baseEnd_5700067] using wordTrace_append hprefix tailTrace_5700067
  have hstable : (prefixWord ++ tailWord_5700067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5700067).length < 2 ^ (prefixWord ++ tailWord_5700067).sum := by decide
  have hdescent : baseEnd_5700067 < baseStart_5700067 := by decide
  rcases family_descends (prefixWord ++ tailWord_5700067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5700090 : List Nat := [3, 1, 1, 1, 1, 2, 2, 6, 6]
def baseStart_5700090 : Nat := 118140960795 + 5700090 * 2 ^ 59
def prefixEnd_5700090 : Nat := 4983230072969 + 3 ^ 40 * 5700090 * 2
def baseEnd_5700090 : Nat := 325209549320745400595641

theorem tailTrace_5700090 : CollatzResearch.WordTrace tailWord_5700090 prefixEnd_5700090 325209549320745400595641 := by
  unfold tailWord_5700090
  simp only [CollatzResearch.WordTrace]
  refine ⟨51974840479888725678246431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138599574613036601808657149 51974840479888725678246431)
  ·
    refine ⟨77962260719833088517369647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51974840479888725678246431 77962260719833088517369647)
    ·
      refine ⟨116943391079749632776054471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77962260719833088517369647 116943391079749632776054471)
      ·
        refine ⟨175415086619624449164081707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116943391079749632776054471 175415086619624449164081707)
        ·
          refine ⟨263122629929436673746122561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175415086619624449164081707 263122629929436673746122561)
          ·
            refine ⟨197341972447077505309591921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 263122629929436673746122561 197341972447077505309591921)
            ·
              refine ⟨148006479335308128982193941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197341972447077505309591921 148006479335308128982193941)
              ·
                refine ⟨6937803718842568546040341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 148006479335308128982193941 6937803718842568546040341)
                ·
                  refine ⟨325209549320745400595641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6937803718842568546040341 325209549320745400595641)
                  ·
                    rfl

theorem cell23_5700090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 6, 6].length) (baseStart_5700090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5700090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5700090 prefixEnd_5700090 := by exact prefixLift 5700090
  have htrace : WordTrace (prefixWord ++ tailWord_5700090) baseStart_5700090 baseEnd_5700090 := by
    simpa [prefixWord, tailWord_5700090, baseEnd_5700090] using wordTrace_append hprefix tailTrace_5700090
  have hstable : (prefixWord ++ tailWord_5700090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5700090).length < 2 ^ (prefixWord ++ tailWord_5700090).sum := by decide
  have hdescent : baseEnd_5700090 < baseStart_5700090 := by decide
  rcases family_descends (prefixWord ++ tailWord_5700090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5700128 : List Nat := [2, 1, 1, 6, 2, 2, 1, 3, 1, 4]
def baseStart_5700128 : Nat := 118140960795 + 5700128 * 2 ^ 59
def prefixEnd_5700128 : Nat := 4983230072969 + 3 ^ 40 * 5700128 * 2
def baseEnd_5700128 : Nat := 975635152050526485561865

theorem tailTrace_5700128 : CollatzResearch.WordTrace tailWord_5700128 prefixEnd_5700128 975635152050526485561865 := by
  unfold tailWord_5700128
  simp only [CollatzResearch.WordTrace]
  refine ⟨103950373946708617601434519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138600498595611490135246025 103950373946708617601434519)
  ·
    refine ⟨155925560920062926402151779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103950373946708617601434519 155925560920062926402151779)
    ·
      refine ⟨233888341380094389603227669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155925560920062926402151779 233888341380094389603227669)
      ·
        refine ⟨10963516002191924512651297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 233888341380094389603227669 10963516002191924512651297)
        ·
          refine ⟨8222637001643943384488473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10963516002191924512651297 8222637001643943384488473)
          ·
            refine ⟨6166977751232957538366355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8222637001643943384488473 6166977751232957538366355)
            ·
              refine ⟨9250466626849436307549533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6166977751232957538366355 9250466626849436307549533)
              ·
                refine ⟨3468924985068538615331075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9250466626849436307549533 3468924985068538615331075)
                ·
                  refine ⟨5203387477602807922996613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3468924985068538615331075 5203387477602807922996613)
                  ·
                    refine ⟨975635152050526485561865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5203387477602807922996613 975635152050526485561865)
                    ·
                      rfl

theorem cell23_5700128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 3, 1, 4].length) (baseStart_5700128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5700128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5700128 prefixEnd_5700128 := by exact prefixLift 5700128
  have htrace : WordTrace (prefixWord ++ tailWord_5700128) baseStart_5700128 baseEnd_5700128 := by
    simpa [prefixWord, tailWord_5700128, baseEnd_5700128] using wordTrace_append hprefix tailTrace_5700128
  have hstable : (prefixWord ++ tailWord_5700128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5700128).length < 2 ^ (prefixWord ++ tailWord_5700128).sum := by decide
  have hdescent : baseEnd_5700128 < baseStart_5700128 := by decide
  rcases family_descends (prefixWord ++ tailWord_5700128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5700158 : List Nat := [4, 2, 1, 4, 1, 2, 2, 1, 6]
def baseStart_5700158 : Nat := 118140960795 + 5700158 * 2 ^ 59
def prefixEnd_5700158 : Nat := 4983230072969 + 3 ^ 40 * 5700158 * 2
def baseEnd_5700158 : Nat := 325213428952357148812273

theorem tailTrace_5700158 : CollatzResearch.WordTrace tailWord_5700158 prefixEnd_5700158 325213428952357148812273 := by
  unfold tailWord_5700158
  simp only [CollatzResearch.WordTrace]
  refine ⟨25987730260413568790807641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138601228055539033550974085 25987730260413568790807641)
  ·
    refine ⟨19490797695310176593105731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25987730260413568790807641 19490797695310176593105731)
    ·
      refine ⟨29236196542965264889658597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19490797695310176593105731 29236196542965264889658597)
      ·
        refine ⟨5481786851805987166810987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29236196542965264889658597 5481786851805987166810987)
        ·
          refine ⟨8222680277708980750216481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5481786851805987166810987 8222680277708980750216481)
          ·
            refine ⟨6167010208281735562662361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8222680277708980750216481 6167010208281735562662361)
            ·
              refine ⟨4625257656211301671996771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6167010208281735562662361 4625257656211301671996771)
              ·
                refine ⟨6937886484316952507995157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4625257656211301671996771 6937886484316952507995157)
                ·
                  refine ⟨325213428952357148812273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6937886484316952507995157 325213428952357148812273)
                  ·
                    rfl

theorem cell23_5700158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 1, 6].length) (baseStart_5700158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5700158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5700158 prefixEnd_5700158 := by exact prefixLift 5700158
  have htrace : WordTrace (prefixWord ++ tailWord_5700158) baseStart_5700158 baseEnd_5700158 := by
    simpa [prefixWord, tailWord_5700158, baseEnd_5700158] using wordTrace_append hprefix tailTrace_5700158
  have hstable : (prefixWord ++ tailWord_5700158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5700158).length < 2 ^ (prefixWord ++ tailWord_5700158).sum := by decide
  have hdescent : baseEnd_5700158 < baseStart_5700158 := by decide
  rcases family_descends (prefixWord ++ tailWord_5700158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5700174 : List Nat := [4, 1, 1, 1, 1, 2, 5, 2, 1, 1, 4]
def baseStart_5700174 : Nat := 118140960795 + 5700174 * 2 ^ 59
def prefixEnd_5700174 : Nat := 4983230072969 + 3 ^ 40 * 5700174 * 2
def baseEnd_5700174 : Nat := 2926929076261686276710383

theorem tailTrace_5700174 : CollatzResearch.WordTrace tailWord_5700174 prefixEnd_5700174 2926929076261686276710383 := by
  unfold tailWord_5700174
  simp only [CollatzResearch.WordTrace]
  refine ⟨25987803206406323132380447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138601617100833723372695717 25987803206406323132380447)
  ·
    refine ⟨38981704809609484698570671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25987803206406323132380447 38981704809609484698570671)
    ·
      refine ⟨58472557214414227047856007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38981704809609484698570671 58472557214414227047856007)
      ·
        refine ⟨87708835821621340571784011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58472557214414227047856007 87708835821621340571784011)
        ·
          refine ⟨131563253732432010857676017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87708835821621340571784011 131563253732432010857676017)
          ·
            refine ⟨98672440299324008143257013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131563253732432010857676017 98672440299324008143257013)
            ·
              refine ⟨9250541278061625763430345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 98672440299324008143257013 9250541278061625763430345)
              ·
                refine ⟨6937905958546219322572759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9250541278061625763430345 6937905958546219322572759)
                ·
                  refine ⟨10406858937819328983859139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6937905958546219322572759 10406858937819328983859139)
                  ·
                    refine ⟨15610288406728993475788709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10406858937819328983859139 15610288406728993475788709)
                    ·
                      refine ⟨2926929076261686276710383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15610288406728993475788709 2926929076261686276710383)
                      ·
                        rfl

theorem cell23_5700174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 2, 1, 1, 4].length) (baseStart_5700174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5700174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5700174 prefixEnd_5700174 := by exact prefixLift 5700174
  have htrace : WordTrace (prefixWord ++ tailWord_5700174) baseStart_5700174 baseEnd_5700174 := by
    simpa [prefixWord, tailWord_5700174, baseEnd_5700174] using wordTrace_append hprefix tailTrace_5700174
  have hstable : (prefixWord ++ tailWord_5700174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5700174).length < 2 ^ (prefixWord ++ tailWord_5700174).sum := by decide
  have hdescent : baseEnd_5700174 < baseStart_5700174 := by decide
  rcases family_descends (prefixWord ++ tailWord_5700174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5700197 : List Nat := [1, 3, 1, 3, 5, 10]
def baseStart_5700197 : Nat := 118140960795 + 5700197 * 2 ^ 59
def prefixEnd_5700197 : Nat := 4983230072969 + 3 ^ 40 * 5700197 * 2
def baseEnd_5700197 : Nat := 12045024223525677723139

theorem tailTrace_5700197 : CollatzResearch.WordTrace tailWord_5700197 prefixEnd_5700197 12045024223525677723139 := by
  unfold tailWord_5700197
  simp only [CollatzResearch.WordTrace]
  refine ⟨207903264530167259987130845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138602176353444839991420563 207903264530167259987130845)
  ·
    refine ⟨77963724198812722495174067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207903264530167259987130845 77963724198812722495174067)
    ·
      refine ⟨116945586298219083742761101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77963724198812722495174067 116945586298219083742761101)
      ·
        refine ⟨43854594861832156403535413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116945586298219083742761101 43854594861832156403535413)
        ·
          refine ⟨4111368268296764662831445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43854594861832156403535413 4111368268296764662831445)
          ·
            refine ⟨12045024223525677723139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4111368268296764662831445 12045024223525677723139)
            ·
              rfl

theorem cell23_5700197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 10].length) (baseStart_5700197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5700197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5700197 prefixEnd_5700197 := by exact prefixLift 5700197
  have htrace : WordTrace (prefixWord ++ tailWord_5700197) baseStart_5700197 baseEnd_5700197 := by
    simpa [prefixWord, tailWord_5700197, baseEnd_5700197] using wordTrace_append hprefix tailTrace_5700197
  have hstable : (prefixWord ++ tailWord_5700197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5700197).length < 2 ^ (prefixWord ++ tailWord_5700197).sum := by decide
  have hdescent : baseEnd_5700197 < baseStart_5700197 := by decide
  rcases family_descends (prefixWord ++ tailWord_5700197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5700224 : List Nat := [2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 3]
def baseStart_5700224 : Nat := 118140960795 + 5700224 * 2 ^ 59
def prefixEnd_5700224 : Nat := 4983230072969 + 3 ^ 40 * 5700224 * 2
def baseEnd_5700224 : Nat := 2926954750294411081085153

theorem tailTrace_5700224 : CollatzResearch.WordTrace tailWord_5700224 prefixEnd_5700224 2926954750294411081085153 := by
  unfold tailWord_5700224
  simp only [CollatzResearch.WordTrace]
  refine ⟨103952124650534721799181863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138602832867379629065575817 103952124650534721799181863)
  ·
    refine ⟨155928186975802082698772795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103952124650534721799181863 155928186975802082698772795)
    ·
      refine ⟨233892280463703124048159193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155928186975802082698772795 233892280463703124048159193)
      ·
        refine ⟨175419210347777343036119395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233892280463703124048159193 175419210347777343036119395)
        ·
          refine ⟨263128815521666014554179093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175419210347777343036119395 263128815521666014554179093)
          ·
            refine ⟨12334163227578094432227145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 263128815521666014554179093 12334163227578094432227145)
            ·
              refine ⟨9250622420683570824170359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12334163227578094432227145 9250622420683570824170359)
              ·
                refine ⟨13875933631025356236255539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9250622420683570824170359 13875933631025356236255539)
                ·
                  refine ⟨20813900446538034354383309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13875933631025356236255539 20813900446538034354383309)
                  ·
                    refine ⟨7805212667451762882893741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20813900446538034354383309 7805212667451762882893741)
                    ·
                      refine ⟨2926954750294411081085153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7805212667451762882893741 2926954750294411081085153)
                      ·
                        rfl

theorem cell23_5700224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 3].length) (baseStart_5700224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5700224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5700224 prefixEnd_5700224 := by exact prefixLift 5700224
  have htrace : WordTrace (prefixWord ++ tailWord_5700224) baseStart_5700224 baseEnd_5700224 := by
    simpa [prefixWord, tailWord_5700224, baseEnd_5700224] using wordTrace_append hprefix tailTrace_5700224
  have hstable : (prefixWord ++ tailWord_5700224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5700224).length < 2 ^ (prefixWord ++ tailWord_5700224).sum := by decide
  have hdescent : baseEnd_5700224 < baseStart_5700224 := by decide
  rcases family_descends (prefixWord ++ tailWord_5700224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5700287 : List Nat := [1, 1, 2, 2, 2, 4, 2, 2, 7]
def baseStart_5700287 : Nat := 118140960795 + 5700287 * 2 ^ 59
def prefixEnd_5700287 : Nat := 4983230072969 + 3 ^ 40 * 5700287 * 2
def baseEnd_5700287 : Nat := 325220788841738259399707

theorem tailTrace_5700287 : CollatzResearch.WordTrace tailWord_5700287 prefixEnd_5700287 325220788841738259399707 := by
  unfold tailWord_5700287
  simp only [CollatzResearch.WordTrace]
  refine ⟨207906547099841205357907115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138604364733227470238604743 207906547099841205357907115)
  ·
    refine ⟨311859820649761808036860673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207906547099841205357907115 311859820649761808036860673)
    ·
      refine ⟨233894865487321356027645505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311859820649761808036860673 233894865487321356027645505)
      ·
        refine ⟨175421149115491017020734129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233894865487321356027645505 175421149115491017020734129)
        ·
          refine ⟨131565861836618262765550597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175421149115491017020734129 131565861836618262765550597)
          ·
            refine ⟨24668599094365924268540737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 131565861836618262765550597 24668599094365924268540737)
            ·
              refine ⟨18501449320774443201405553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24668599094365924268540737 18501449320774443201405553)
              ·
                refine ⟨13876086990580832401054165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18501449320774443201405553 13876086990580832401054165)
                ·
                  refine ⟨325220788841738259399707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13876086990580832401054165 325220788841738259399707)
                  ·
                    rfl

theorem cell23_5700287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2, 7].length) (baseStart_5700287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5700287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5700287 prefixEnd_5700287 := by exact prefixLift 5700287
  have htrace : WordTrace (prefixWord ++ tailWord_5700287) baseStart_5700287 baseEnd_5700287 := by
    simpa [prefixWord, tailWord_5700287, baseEnd_5700287] using wordTrace_append hprefix tailTrace_5700287
  have hstable : (prefixWord ++ tailWord_5700287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5700287).length < 2 ^ (prefixWord ++ tailWord_5700287).sum := by decide
  have hdescent : baseEnd_5700287 < baseStart_5700287 := by decide
  rcases family_descends (prefixWord ++ tailWord_5700287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5700367 : List Nat := [1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 6]
def baseStart_5700367 : Nat := 118140960795 + 5700367 * 2 ^ 59
def prefixEnd_5700367 : Nat := 4983230072969 + 3 ^ 40 * 5700367 * 2
def baseEnd_5700367 : Nat := 2927028178028004021596995

theorem tailTrace_5700367 : CollatzResearch.WordTrace tailWord_5700367 prefixEnd_5700367 2927028178028004021596995 := by
  unfold tailWord_5700367
  simp only [CollatzResearch.WordTrace]
  refine ⟨207909464939551379020819355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138606309959700919347212903 207909464939551379020819355)
  ·
    refine ⟨311864197409327068531229033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207909464939551379020819355 311864197409327068531229033)
    ·
      refine ⟨233898148056995301398421775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311864197409327068531229033 233898148056995301398421775)
      ·
        refine ⟨350847222085492952097632663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233898148056995301398421775 350847222085492952097632663)
        ·
          refine ⟨526270833128239428146448995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350847222085492952097632663 526270833128239428146448995)
          ·
            refine ⟨789406249692359142219673493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 526270833128239428146448995 789406249692359142219673493)
            ·
              refine ⟨37003417954329334791547195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 789406249692359142219673493 37003417954329334791547195)
              ·
                refine ⟨55505126931494002187320793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37003417954329334791547195 55505126931494002187320793)
                ·
                  refine ⟨41628845198620501640490595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55505126931494002187320793 41628845198620501640490595)
                  ·
                    refine ⟨62443267797930752460735893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41628845198620501640490595 62443267797930752460735893)
                    ·
                      refine ⟨2927028178028004021596995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62443267797930752460735893 2927028178028004021596995)
                      ·
                        rfl

theorem cell23_5700367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 6].length) (baseStart_5700367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5700367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5700367 prefixEnd_5700367 := by exact prefixLift 5700367
  have htrace : WordTrace (prefixWord ++ tailWord_5700367) baseStart_5700367 baseEnd_5700367 := by
    simpa [prefixWord, tailWord_5700367, baseEnd_5700367] using wordTrace_append hprefix tailTrace_5700367
  have hstable : (prefixWord ++ tailWord_5700367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5700367).length < 2 ^ (prefixWord ++ tailWord_5700367).sum := by decide
  have hdescent : baseEnd_5700367 < baseStart_5700367 := by decide
  rcases family_descends (prefixWord ++ tailWord_5700367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5700388 : List Nat := [2, 3, 1, 3, 3, 1, 1, 1, 2, 4, 2]
def baseStart_5700388 : Nat := 118140960795 + 5700388 * 2 ^ 59
def prefixEnd_5700388 : Nat := 4983230072969 + 3 ^ 40 * 5700388 * 2
def baseEnd_5700388 : Nat := 2927038961121748439434399

theorem tailTrace_5700388 : CollatzResearch.WordTrace tailWord_5700388 prefixEnd_5700388 2927038961121748439434399 := by
  unfold tailWord_5700388
  simp only [CollatzResearch.WordTrace]
  refine ⟨103955115436237649803666909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138606820581650199738222545 103955115436237649803666909)
  ·
    refine ⟨38983168288589118676375091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103955115436237649803666909 38983168288589118676375091)
    ·
      refine ⟨58474752432883678014562637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38983168288589118676375091 58474752432883678014562637)
      ·
        refine ⟨21928032162331379255460989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58474752432883678014562637 21928032162331379255460989)
        ·
          refine ⟨8223012060874267220797871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21928032162331379255460989 8223012060874267220797871)
          ·
            refine ⟨12334518091311400831196807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8223012060874267220797871 12334518091311400831196807)
            ·
              refine ⟨18501777136967101246795211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12334518091311400831196807 18501777136967101246795211)
              ·
                refine ⟨27752665705450651870192817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18501777136967101246795211 27752665705450651870192817)
                ·
                  refine ⟨20814499279087988902644613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27752665705450651870192817 20814499279087988902644613)
                  ·
                    refine ⟨3902718614828997919245865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20814499279087988902644613 3902718614828997919245865)
                    ·
                      refine ⟨2927038961121748439434399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3902718614828997919245865 2927038961121748439434399)
                      ·
                        rfl

theorem cell23_5700388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_5700388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5700388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5700388 prefixEnd_5700388 := by exact prefixLift 5700388
  have htrace : WordTrace (prefixWord ++ tailWord_5700388) baseStart_5700388 baseEnd_5700388 := by
    simpa [prefixWord, tailWord_5700388, baseEnd_5700388] using wordTrace_append hprefix tailTrace_5700388
  have hstable : (prefixWord ++ tailWord_5700388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5700388).length < 2 ^ (prefixWord ++ tailWord_5700388).sum := by decide
  have hdescent : baseEnd_5700388 < baseStart_5700388 := by decide
  rcases family_descends (prefixWord ++ tailWord_5700388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5700398 : List Nat := [4, 1, 3, 2, 1, 2, 1, 2, 3, 4]
def baseStart_5700398 : Nat := 118140960795 + 5700398 * 2 ^ 59
def prefixEnd_5700398 : Nat := 4983230072969 + 3 ^ 40 * 5700398 * 2
def baseEnd_5700398 : Nat := 975681365309431133436451

theorem tailTrace_5700398 : CollatzResearch.WordTrace tailWord_5700398 prefixEnd_5700398 975681365309431133436451 := by
  unfold tailWord_5700398
  simp only [CollatzResearch.WordTrace]
  refine ⟨25988824450304883914399731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138607063734959380876798565 25988824450304883914399731)
  ·
    refine ⟨38983236675457325871599597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25988824450304883914399731 38983236675457325871599597)
    ·
      refine ⟨14618713753296497201849849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38983236675457325871599597 14618713753296497201849849)
      ·
        refine ⟨10964035314972372901387387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14618713753296497201849849 10964035314972372901387387)
        ·
          refine ⟨16446052972458559352081081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10964035314972372901387387 16446052972458559352081081)
          ·
            refine ⟨12334539729343919514060811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16446052972458559352081081 12334539729343919514060811)
            ·
              refine ⟨18501809594015879271091217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12334539729343919514060811 18501809594015879271091217)
              ·
                refine ⟨13876357195511909453318413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18501809594015879271091217 13876357195511909453318413)
                ·
                  refine ⟨5203633948316966044994405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13876357195511909453318413 5203633948316966044994405)
                  ·
                    refine ⟨975681365309431133436451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5203633948316966044994405 975681365309431133436451)
                    ·
                      rfl

theorem cell23_5700398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_5700398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5700398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5700398 prefixEnd_5700398 := by exact prefixLift 5700398
  have htrace : WordTrace (prefixWord ++ tailWord_5700398) baseStart_5700398 baseEnd_5700398 := by
    simpa [prefixWord, tailWord_5700398, baseEnd_5700398] using wordTrace_append hprefix tailTrace_5700398
  have hstable : (prefixWord ++ tailWord_5700398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5700398).length < 2 ^ (prefixWord ++ tailWord_5700398).sum := by decide
  have hdescent : baseEnd_5700398 < baseStart_5700398 := by decide
  rcases family_descends (prefixWord ++ tailWord_5700398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5700461 : List Nat := [1, 5, 1, 1, 1, 1, 1, 1, 1, 8, 2]
def baseStart_5700461 : Nat := 118140960795 + 5700461 * 2 ^ 59
def prefixEnd_5700461 : Nat := 4983230072969 + 3 ^ 40 * 5700461 * 2
def baseEnd_5700461 : Nat := 2927076445209526653821563

theorem tailTrace_5700461 : CollatzResearch.WordTrace tailWord_5700461 prefixEnd_5700461 2927076445209526653821563 := by
  unfold tailWord_5700461
  simp only [CollatzResearch.WordTrace]
  refine ⟨207912893401210833074741237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138608595600807222049827491 207912893401210833074741237)
  ·
    refine ⟨19491833756363515600756991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 207912893401210833074741237 19491833756363515600756991)
    ·
      refine ⟨29237750634545273401135487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19491833756363515600756991 29237750634545273401135487)
      ·
        refine ⟨43856625951817910101703231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29237750634545273401135487 43856625951817910101703231)
        ·
          refine ⟨65784938927726865152554847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43856625951817910101703231 65784938927726865152554847)
          ·
            refine ⟨98677408391590297728832271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65784938927726865152554847 98677408391590297728832271)
            ·
              refine ⟨148016112587385446593248407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98677408391590297728832271 148016112587385446593248407)
              ·
                refine ⟨222024168881078169889872611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148016112587385446593248407 222024168881078169889872611)
                ·
                  refine ⟨333036253321617254834808917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 222024168881078169889872611 333036253321617254834808917)
                  ·
                    refine ⟨3902768593612702205095417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 333036253321617254834808917 3902768593612702205095417)
                    ·
                      refine ⟨2927076445209526653821563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3902768593612702205095417 2927076445209526653821563)
                      ·
                        rfl

theorem cell23_5700461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 8, 2].length) (baseStart_5700461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5700461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5700461 prefixEnd_5700461 := by exact prefixLift 5700461
  have htrace : WordTrace (prefixWord ++ tailWord_5700461) baseStart_5700461 baseEnd_5700461 := by
    simpa [prefixWord, tailWord_5700461, baseEnd_5700461] using wordTrace_append hprefix tailTrace_5700461
  have hstable : (prefixWord ++ tailWord_5700461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5700461).length < 2 ^ (prefixWord ++ tailWord_5700461).sum := by decide
  have hdescent : baseEnd_5700461 < baseStart_5700461 := by decide
  rcases family_descends (prefixWord ++ tailWord_5700461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5700474 : List Nat := [3, 1, 1, 1, 1, 1, 3, 3, 3, 2, 4]
def baseStart_5700474 : Nat := 118140960795 + 5700474 * 2 ^ 59
def prefixEnd_5700474 : Nat := 4983230072969 + 3 ^ 40 * 5700474 * 2
def baseEnd_5700474 : Nat := 2927083120458035102959003

theorem tailTrace_5700474 : CollatzResearch.WordTrace tailWord_5700474 prefixEnd_5700474 2927083120458035102959003 := by
  unfold tailWord_5700474
  simp only [CollatzResearch.WordTrace]
  refine ⟨51978341887540934073741119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138608911700109157529976317 51978341887540934073741119)
  ·
    refine ⟨77967512831311401110611679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51978341887540934073741119 77967512831311401110611679)
    ·
      refine ⟨116951269246967101665917519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77967512831311401110611679 116951269246967101665917519)
      ·
        refine ⟨175426903870450652498876279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116951269246967101665917519 175426903870450652498876279)
        ·
          refine ⟨263140355805675978748314419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175426903870450652498876279 263140355805675978748314419)
          ·
            refine ⟨394710533708513968122471629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263140355805675978748314419 394710533708513968122471629)
            ·
              refine ⟨148016450140692738045926861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 394710533708513968122471629 148016450140692738045926861)
              ·
                refine ⟨55506168802759776767222573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 148016450140692738045926861 55506168802759776767222573)
                ·
                  refine ⟨20814813301034916287708465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55506168802759776767222573 20814813301034916287708465)
                  ·
                    refine ⟨15611109975776187215781349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20814813301034916287708465 15611109975776187215781349)
                    ·
                      refine ⟨2927083120458035102959003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15611109975776187215781349 2927083120458035102959003)
                      ·
                        rfl

theorem cell23_5700474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 3, 2, 4].length) (baseStart_5700474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5700474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5700474 prefixEnd_5700474 := by exact prefixLift 5700474
  have htrace : WordTrace (prefixWord ++ tailWord_5700474) baseStart_5700474 baseEnd_5700474 := by
    simpa [prefixWord, tailWord_5700474, baseEnd_5700474] using wordTrace_append hprefix tailTrace_5700474
  have hstable : (prefixWord ++ tailWord_5700474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5700474).length < 2 ^ (prefixWord ++ tailWord_5700474).sum := by decide
  have hdescent : baseEnd_5700474 < baseStart_5700474 := by decide
  rcases family_descends (prefixWord ++ tailWord_5700474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5700525 : List Nat := [1, 5, 2, 3, 1, 1, 1, 2, 1, 2, 4]
def baseStart_5700525 : Nat := 118140960795 + 5700525 * 2 ^ 59
def prefixEnd_5700525 : Nat := 4983230072969 + 3 ^ 40 * 5700525 * 2
def baseEnd_5700525 : Nat := 2927109307971414403421269

theorem tailTrace_5700525 : CollatzResearch.WordTrace tailWord_5700525 prefixEnd_5700525 2927109307971414403421269 := by
  unfold tailWord_5700525
  simp only [CollatzResearch.WordTrace]
  refine ⟨207915227672978972005071029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138610151781985981336714019 207915227672978972005071029)
  ·
    refine ⟨19492052594341778625475409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 207915227672978972005071029 19492052594341778625475409)
    ·
      refine ⟨14619039445756333969106557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19492052594341778625475409 14619039445756333969106557)
      ·
        refine ⟨5482139792158625238414959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14619039445756333969106557 5482139792158625238414959)
        ·
          refine ⟨8223209688237937857622439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5482139792158625238414959 8223209688237937857622439)
          ·
            refine ⟨12334814532356906786433659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8223209688237937857622439 12334814532356906786433659)
            ·
              refine ⟨18502221798535360179650489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12334814532356906786433659 18502221798535360179650489)
              ·
                refine ⟨13876666348901520134737867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18502221798535360179650489 13876666348901520134737867)
                ·
                  refine ⟨20814999523352280202106801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13876666348901520134737867 20814999523352280202106801)
                  ·
                    refine ⟨15611249642514210151580101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20814999523352280202106801 15611249642514210151580101)
                    ·
                      refine ⟨2927109307971414403421269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15611249642514210151580101 2927109307971414403421269)
                      ·
                        rfl

theorem cell23_5700525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_5700525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5700525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5700525 prefixEnd_5700525 := by exact prefixLift 5700525
  have htrace : WordTrace (prefixWord ++ tailWord_5700525) baseStart_5700525 baseEnd_5700525 := by
    simpa [prefixWord, tailWord_5700525, baseEnd_5700525] using wordTrace_append hprefix tailTrace_5700525
  have hstable : (prefixWord ++ tailWord_5700525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5700525).length < 2 ^ (prefixWord ++ tailWord_5700525).sum := by decide
  have hdescent : baseEnd_5700525 < baseStart_5700525 := by decide
  rcases family_descends (prefixWord ++ tailWord_5700525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5700568 : List Nat := [2, 1, 2, 2, 2, 3, 1, 3, 1, 4, 2]
def baseStart_5700568 : Nat := 118140960795 + 5700568 * 2 ^ 59
def prefixEnd_5700568 : Nat := 4983230072969 + 3 ^ 40 * 5700568 * 2
def baseEnd_5700568 : Nat := 2927131387639557735183571

theorem tailTrace_5700568 : CollatzResearch.WordTrace tailWord_5700568 prefixEnd_5700568 2927131387639557735183571 := by
  unfold tailWord_5700568
  simp only [CollatzResearch.WordTrace]
  refine ⟨103958398005911595174443179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138611197341215460232590905 103958398005911595174443179)
  ·
    refine ⟨155937597008867392761664769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103958398005911595174443179 155937597008867392761664769)
    ·
      refine ⟨116953197756650544571248577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155937597008867392761664769 116953197756650544571248577)
      ·
        refine ⟨87714898317487908428436433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116953197756650544571248577 87714898317487908428436433)
        ·
          refine ⟨65786173738115931321327325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87714898317487908428436433 65786173738115931321327325)
          ·
            refine ⟨24669815151793474245497747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65786173738115931321327325 24669815151793474245497747)
            ·
              refine ⟨37004722727690211368246621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24669815151793474245497747 37004722727690211368246621)
              ·
                refine ⟨13876771022883829263092483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37004722727690211368246621 13876771022883829263092483)
                ·
                  refine ⟨20815156534325743894638725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13876771022883829263092483 20815156534325743894638725)
                  ·
                    refine ⟨3902841850186076980244761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20815156534325743894638725 3902841850186076980244761)
                    ·
                      refine ⟨2927131387639557735183571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3902841850186076980244761 2927131387639557735183571)
                      ·
                        rfl

theorem cell23_5700568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3, 1, 4, 2].length) (baseStart_5700568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5700568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5700568 prefixEnd_5700568 := by exact prefixLift 5700568
  have htrace : WordTrace (prefixWord ++ tailWord_5700568) baseStart_5700568 baseEnd_5700568 := by
    simpa [prefixWord, tailWord_5700568, baseEnd_5700568] using wordTrace_append hprefix tailTrace_5700568
  have hstable : (prefixWord ++ tailWord_5700568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5700568).length < 2 ^ (prefixWord ++ tailWord_5700568).sum := by decide
  have hdescent : baseEnd_5700568 < baseStart_5700568 := by decide
  rcases family_descends (prefixWord ++ tailWord_5700568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5700596 : List Nat := [2, 6, 2, 1, 1, 1, 1, 1, 4, 1, 3]
def baseStart_5700596 : Nat := 118140960795 + 5700596 * 2 ^ 59
def prefixEnd_5700596 : Nat := 4983230072969 + 3 ^ 40 * 5700596 * 2
def baseEnd_5700596 : Nat := 2927145765097883625633443

theorem tailTrace_5700596 : CollatzResearch.WordTrace tailWord_5700596 prefixEnd_5700596 2927145765097883625633443 := by
  unfold tailWord_5700596
  simp only [CollatzResearch.WordTrace]
  refine ⟨103958908627860875565452821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138611878170481167420603761 103958908627860875565452821)
  ·
    refine ⟨4873073841930978542130601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 103958908627860875565452821 4873073841930978542130601)
    ·
      refine ⟨3654805381448233906597951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4873073841930978542130601 3654805381448233906597951)
      ·
        refine ⟨5482208072172350859896927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3654805381448233906597951 5482208072172350859896927)
        ·
          refine ⟨8223312108258526289845391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5482208072172350859896927 8223312108258526289845391)
          ·
            refine ⟨12334968162387789434768087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8223312108258526289845391 12334968162387789434768087)
            ·
              refine ⟨18502452243581684152152131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12334968162387789434768087 18502452243581684152152131)
              ·
                refine ⟨27753678365372526228228197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18502452243581684152152131 27753678365372526228228197)
                ·
                  refine ⟨5203814693507348667792787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27753678365372526228228197 5203814693507348667792787)
                  ·
                    refine ⟨7805722040261023001689181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5203814693507348667792787 7805722040261023001689181)
                    ·
                      refine ⟨2927145765097883625633443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7805722040261023001689181 2927145765097883625633443)
                      ·
                        rfl

theorem cell23_5700596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_5700596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5700596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5700596 prefixEnd_5700596 := by exact prefixLift 5700596
  have htrace : WordTrace (prefixWord ++ tailWord_5700596) baseStart_5700596 baseEnd_5700596 := by
    simpa [prefixWord, tailWord_5700596, baseEnd_5700596] using wordTrace_append hprefix tailTrace_5700596
  have hstable : (prefixWord ++ tailWord_5700596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5700596).length < 2 ^ (prefixWord ++ tailWord_5700596).sum := by decide
  have hdescent : baseEnd_5700596 < baseStart_5700596 := by decide
  rcases family_descends (prefixWord ++ tailWord_5700596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5700598 : List Nat := [5, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4]
def baseStart_5700598 : Nat := 118140960795 + 5700598 * 2 ^ 59
def prefixEnd_5700598 : Nat := 4983230072969 + 3 ^ 40 * 5700598 * 2
def baseEnd_5700598 : Nat := 2927146792059192617808433

theorem tailTrace_5700598 : CollatzResearch.WordTrace tailWord_5700598 prefixEnd_5700598 2927146792059192617808433 := by
  unfold tailWord_5700598
  simp only [CollatzResearch.WordTrace]
  refine ⟨12994868137607156592029903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 138611926801143003648318965 12994868137607156592029903)
  ·
    refine ⟨19492302206410734888044855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12994868137607156592029903 19492302206410734888044855)
    ·
      refine ⟨29238453309616102332067283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19492302206410734888044855 29238453309616102332067283)
      ·
        refine ⟨43857679964424153498100925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29238453309616102332067283 43857679964424153498100925)
        ·
          refine ⟨16446629986659057561787847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43857679964424153498100925 16446629986659057561787847)
          ·
            refine ⟨24669944979988586342681771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16446629986659057561787847 24669944979988586342681771)
            ·
              refine ⟨37004917469982879514022657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24669944979988586342681771 37004917469982879514022657)
              ·
                refine ⟨27753688102487159635516993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37004917469982879514022657 27753688102487159635516993)
                ·
                  refine ⟨20815266076865369726637745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27753688102487159635516993 20815266076865369726637745)
                  ·
                    refine ⟨15611449557649027294978309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20815266076865369726637745 15611449557649027294978309)
                    ·
                      refine ⟨2927146792059192617808433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15611449557649027294978309 2927146792059192617808433)
                      ·
                        rfl

theorem cell23_5700598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_5700598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5700598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5700598 prefixEnd_5700598 := by exact prefixLift 5700598
  have htrace : WordTrace (prefixWord ++ tailWord_5700598) baseStart_5700598 baseEnd_5700598 := by
    simpa [prefixWord, tailWord_5700598, baseEnd_5700598] using wordTrace_append hprefix tailTrace_5700598
  have hstable : (prefixWord ++ tailWord_5700598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5700598).length < 2 ^ (prefixWord ++ tailWord_5700598).sum := by decide
  have hdescent : baseEnd_5700598 < baseStart_5700598 := by decide
  rcases family_descends (prefixWord ++ tailWord_5700598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5700601 : List Nat := [1, 2, 1, 3, 1, 3, 1, 1, 4, 3, 3]
def baseStart_5700601 : Nat := 118140960795 + 5700601 * 2 ^ 59
def prefixEnd_5700601 : Nat := 4983230072969 + 3 ^ 40 * 5700601 * 2
def baseEnd_5700601 : Nat := 2927148332501156106070919

theorem tailTrace_5700601 : CollatzResearch.WordTrace tailWord_5700601 prefixEnd_5700601 2927148332501156106070919 := by
  unfold tailWord_5700601
  simp only [CollatzResearch.WordTrace]
  refine ⟨207917999620703636984837657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138611999747135757989891771 207917999620703636984837657)
  ·
    refine ⟨155938499715527727738628243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207917999620703636984837657 155938499715527727738628243)
    ·
      refine ⟨233907749573291591607942365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155938499715527727738628243 233907749573291591607942365)
      ·
        refine ⟨87715406089984346852978387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 233907749573291591607942365 87715406089984346852978387)
        ·
          refine ⟨131573109134976520279467581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87715406089984346852978387 131573109134976520279467581)
          ·
            refine ⟨49339915925616195104800343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131573109134976520279467581 49339915925616195104800343)
            ·
              refine ⟨74009873888424292657200515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49339915925616195104800343 74009873888424292657200515)
              ·
                refine ⟨111014810832636438985800773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74009873888424292657200515 111014810832636438985800773)
                ·
                  refine ⟨20815277031119332309837645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 111014810832636438985800773 20815277031119332309837645)
                  ·
                    refine ⟨7805728886669749616189117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20815277031119332309837645 7805728886669749616189117)
                    ·
                      refine ⟨2927148332501156106070919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7805728886669749616189117 2927148332501156106070919)
                      ·
                        rfl

theorem cell23_5700601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4, 3, 3].length) (baseStart_5700601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5700601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5700601 prefixEnd_5700601 := by exact prefixLift 5700601
  have htrace : WordTrace (prefixWord ++ tailWord_5700601) baseStart_5700601 baseEnd_5700601 := by
    simpa [prefixWord, tailWord_5700601, baseEnd_5700601] using wordTrace_append hprefix tailTrace_5700601
  have hstable : (prefixWord ++ tailWord_5700601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5700601).length < 2 ^ (prefixWord ++ tailWord_5700601).sum := by decide
  have hdescent : baseEnd_5700601 < baseStart_5700601 := by decide
  rcases family_descends (prefixWord ++ tailWord_5700601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5700618 : List Nat := [3, 1, 2, 2, 3, 1, 2, 1, 2, 3, 3]
def baseStart_5700618 : Nat := 118140960795 + 5700618 * 2 ^ 59
def prefixEnd_5700618 : Nat := 4983230072969 + 3 ^ 40 * 5700618 * 2
def baseEnd_5700618 : Nat := 2927157061672282539558341

theorem tailTrace_5700618 : CollatzResearch.WordTrace tailWord_5700618 prefixEnd_5700618 2927157061672282539558341 := by
  unfold tailWord_5700618
  simp only [CollatzResearch.WordTrace]
  refine ⟨51979654915410512222051627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138612413107761365925471005 51979654915410512222051627)
  ·
    refine ⟨77969482373115768333077441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51979654915410512222051627 77969482373115768333077441)
    ·
      refine ⟨58477111779836826249808081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77969482373115768333077441 58477111779836826249808081)
      ·
        refine ⟨43857833834877619687356061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58477111779836826249808081 43857833834877619687356061)
        ·
          refine ⟨16446687688079107382758523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43857833834877619687356061 16446687688079107382758523)
          ·
            refine ⟨24670031532118661074137785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16446687688079107382758523 24670031532118661074137785)
            ·
              refine ⟨18502523649088995805603339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24670031532118661074137785 18502523649088995805603339)
              ·
                refine ⟨27753785473633493708405009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18502523649088995805603339 27753785473633493708405009)
                ·
                  refine ⟨20815339105225120281303757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27753785473633493708405009 20815339105225120281303757)
                  ·
                    refine ⟨7805752164459420105488909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20815339105225120281303757 7805752164459420105488909)
                    ·
                      refine ⟨2927157061672282539558341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7805752164459420105488909 2927157061672282539558341)
                      ·
                        rfl

theorem cell23_5700618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_5700618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5700618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5700618 prefixEnd_5700618 := by exact prefixLift 5700618
  have htrace : WordTrace (prefixWord ++ tailWord_5700618) baseStart_5700618 baseEnd_5700618 := by
    simpa [prefixWord, tailWord_5700618, baseEnd_5700618] using wordTrace_append hprefix tailTrace_5700618
  have hstable : (prefixWord ++ tailWord_5700618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5700618).length < 2 ^ (prefixWord ++ tailWord_5700618).sum := by decide
  have hdescent : baseEnd_5700618 < baseStart_5700618 := by decide
  rcases family_descends (prefixWord ++ tailWord_5700618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5700658 : List Nat := [3, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4]
def baseStart_5700658 : Nat := 118140960795 + 5700658 * 2 ^ 59
def prefixEnd_5700658 : Nat := 4983230072969 + 3 ^ 40 * 5700658 * 2
def baseEnd_5700658 : Nat := 2927177600898462383058157

theorem tailTrace_5700658 : CollatzResearch.WordTrace tailWord_5700658 prefixEnd_5700658 2927177600898462383058157 := by
  unfold tailWord_5700658
  simp only [CollatzResearch.WordTrace]
  refine ⟨51980019645374283929915657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138613385720998090479775085 51980019645374283929915657)
  ·
    refine ⟨38985014734030712947436743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51980019645374283929915657 38985014734030712947436743)
    ·
      refine ⟨58477522101046069421155115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38985014734030712947436743 58477522101046069421155115)
      ·
        refine ⟨87716283151569104131732673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58477522101046069421155115 87716283151569104131732673)
        ·
          refine ⟨65787212363676828098799505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87716283151569104131732673 65787212363676828098799505)
          ·
            refine ⟨49340409272757621074099629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65787212363676828098799505 49340409272757621074099629)
            ·
              refine ⟨18502653477284107902787361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49340409272757621074099629 18502653477284107902787361)
              ·
                refine ⟨13876990107963080927090521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18502653477284107902787361 13876990107963080927090521)
                ·
                  refine ⟨10407742580972310695317891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13876990107963080927090521 10407742580972310695317891)
                  ·
                    refine ⟨15611613871458466042976837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10407742580972310695317891 15611613871458466042976837)
                    ·
                      refine ⟨2927177600898462383058157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15611613871458466042976837 2927177600898462383058157)
                      ·
                        rfl

theorem cell23_5700658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4].length) (baseStart_5700658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5700658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5700658 prefixEnd_5700658 := by exact prefixLift 5700658
  have htrace : WordTrace (prefixWord ++ tailWord_5700658) baseStart_5700658 baseEnd_5700658 := by
    simpa [prefixWord, tailWord_5700658, baseEnd_5700658] using wordTrace_append hprefix tailTrace_5700658
  have hstable : (prefixWord ++ tailWord_5700658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5700658).length < 2 ^ (prefixWord ++ tailWord_5700658).sum := by decide
  have hdescent : baseEnd_5700658 < baseStart_5700658 := by decide
  rcases family_descends (prefixWord ++ tailWord_5700658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5700691 : List Nat := [1, 1, 1, 2, 1, 1, 2, 3, 1, 7, 3]
def baseStart_5700691 : Nat := 118140960795 + 5700691 * 2 ^ 59
def prefixEnd_5700691 : Nat := 4983230072969 + 3 ^ 40 * 5700691 * 2
def baseEnd_5700691 : Nat := 2927194545760060753945505

theorem tailTrace_5700691 : CollatzResearch.WordTrace tailWord_5700691 prefixEnd_5700691 2927194545760060753945505 := by
  unfold tailWord_5700691
  simp only [CollatzResearch.WordTrace]
  refine ⟨207921282190377582355613927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138614188126918388237075951 207921282190377582355613927)
  ·
    refine ⟨311881923285566373533420891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207921282190377582355613927 311881923285566373533420891)
    ·
      refine ⟨467822884928349560300131337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311881923285566373533420891 467822884928349560300131337)
      ·
        refine ⟨350867163696262170225098503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 467822884928349560300131337 350867163696262170225098503)
        ·
          refine ⟨526300745544393255337647755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350867163696262170225098503 526300745544393255337647755)
          ·
            refine ⟨789451118316589883006471633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 526300745544393255337647755 789451118316589883006471633)
            ·
              refine ⟨592088338737442412254853725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 789451118316589883006471633 592088338737442412254853725)
              ·
                refine ⟨222033127026540904595570147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 592088338737442412254853725 222033127026540904595570147)
                ·
                  refine ⟨333049690539811356893355221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 222033127026540904595570147 333049690539811356893355221)
                  ·
                    refine ⟨7805852122026828677188013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 333049690539811356893355221 7805852122026828677188013)
                    ·
                      refine ⟨2927194545760060753945505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7805852122026828677188013 2927194545760060753945505)
                      ·
                        rfl

theorem cell23_5700691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 7, 3].length) (baseStart_5700691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5700691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5700691 prefixEnd_5700691 := by exact prefixLift 5700691
  have htrace : WordTrace (prefixWord ++ tailWord_5700691) baseStart_5700691 baseEnd_5700691 := by
    simpa [prefixWord, tailWord_5700691, baseEnd_5700691] using wordTrace_append hprefix tailTrace_5700691
  have hstable : (prefixWord ++ tailWord_5700691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5700691).length < 2 ^ (prefixWord ++ tailWord_5700691).sum := by decide
  have hdescent : baseEnd_5700691 < baseStart_5700691 := by decide
  rcases family_descends (prefixWord ++ tailWord_5700691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5700759 : List Nat := [1, 1, 3, 3, 3, 2, 2, 3, 1, 1, 3]
def baseStart_5700759 : Nat := 118140960795 + 5700759 * 2 ^ 59
def prefixEnd_5700759 : Nat := 4983230072969 + 3 ^ 40 * 5700759 * 2
def baseEnd_5700759 : Nat := 2927229462444566487895193

theorem tailTrace_5700759 : CollatzResearch.WordTrace tailWord_5700759 prefixEnd_5700759 2927229462444566487895193 := by
  unfold tailWord_5700759
  simp only [CollatzResearch.WordTrace]
  refine ⟨207923762354131229969089331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138615841569420819979392887 207923762354131229969089331)
  ·
    refine ⟨311885643531196844953633997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207923762354131229969089331 311885643531196844953633997)
    ·
      refine ⟨116957116324198816857612749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 311885643531196844953633997 116957116324198816857612749)
      ·
        refine ⟨43858918621574556321604781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116957116324198816857612749 43858918621574556321604781)
        ·
          refine ⟨16447094483090458620601793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43858918621574556321604781 16447094483090458620601793)
          ·
            refine ⟨12335320862317843965451345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16447094483090458620601793 12335320862317843965451345)
            ·
              refine ⟨9251490646738382974088509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12335320862317843965451345 9251490646738382974088509)
              ·
                refine ⟨3469308992526893615283191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9251490646738382974088509 3469308992526893615283191)
                ·
                  refine ⟨5203963488790340422924787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3469308992526893615283191 5203963488790340422924787)
                  ·
                    refine ⟨7805945233185510634387181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5203963488790340422924787 7805945233185510634387181)
                    ·
                      refine ⟨2927229462444566487895193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7805945233185510634387181 2927229462444566487895193)
                      ·
                        rfl

theorem cell23_5700759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 3, 1, 1, 3].length) (baseStart_5700759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5700759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5700759 prefixEnd_5700759 := by exact prefixLift 5700759
  have htrace : WordTrace (prefixWord ++ tailWord_5700759) baseStart_5700759 baseEnd_5700759 := by
    simpa [prefixWord, tailWord_5700759, baseEnd_5700759] using wordTrace_append hprefix tailTrace_5700759
  have hstable : (prefixWord ++ tailWord_5700759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5700759).length < 2 ^ (prefixWord ++ tailWord_5700759).sum := by decide
  have hdescent : baseEnd_5700759 < baseStart_5700759 := by decide
  rcases family_descends (prefixWord ++ tailWord_5700759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5700761 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 5, 1, 6]
def baseStart_5700761 : Nat := 118140960795 + 5700761 * 2 ^ 59
def prefixEnd_5700761 : Nat := 4983230072969 + 3 ^ 40 * 5700761 * 2
def baseEnd_5700761 : Nat := 2927230489405875480070183

theorem tailTrace_5700761 : CollatzResearch.WordTrace tailWord_5700761 prefixEnd_5700761 2927230489405875480070183 := by
  unfold tailWord_5700761
  simp only [CollatzResearch.WordTrace]
  refine ⟨207923835300123984310662137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138615890200082656207108091 207923835300123984310662137)
  ·
    refine ⟨155942876475092988232996603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207923835300123984310662137 155942876475092988232996603)
    ·
      refine ⟨233914314712639482349494905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155942876475092988232996603 233914314712639482349494905)
      ·
        refine ⟨175435736034479611762121179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233914314712639482349494905 175435736034479611762121179)
        ·
          refine ⟨263153604051719417643181769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175435736034479611762121179 263153604051719417643181769)
          ·
            refine ⟨197365203038789563232386327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 263153604051719417643181769 197365203038789563232386327)
            ·
              refine ⟨296047804558184344848579491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197365203038789563232386327 296047804558184344848579491)
              ·
                refine ⟨444071706837276517272869237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 296047804558184344848579491 444071706837276517272869237)
                ·
                  refine ⟨41631722515994673494331491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 444071706837276517272869237 41631722515994673494331491)
                  ·
                    refine ⟨62447583773992010241497237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41631722515994673494331491 62447583773992010241497237)
                    ·
                      refine ⟨2927230489405875480070183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62447583773992010241497237 2927230489405875480070183)
                      ·
                        rfl

theorem cell23_5700761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 1, 6].length) (baseStart_5700761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5700761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5700761 prefixEnd_5700761 := by exact prefixLift 5700761
  have htrace : WordTrace (prefixWord ++ tailWord_5700761) baseStart_5700761 baseEnd_5700761 := by
    simpa [prefixWord, tailWord_5700761, baseEnd_5700761] using wordTrace_append hprefix tailTrace_5700761
  have hstable : (prefixWord ++ tailWord_5700761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5700761).length < 2 ^ (prefixWord ++ tailWord_5700761).sum := by decide
  have hdescent : baseEnd_5700761 < baseStart_5700761 := by decide
  rcases family_descends (prefixWord ++ tailWord_5700761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5700762 : List Nat := [3, 1, 1, 5, 1, 1, 4, 1, 1, 5]
def baseStart_5700762 : Nat := 118140960795 + 5700762 * 2 ^ 59
def prefixEnd_5700762 : Nat := 4983230072969 + 3 ^ 40 * 5700762 * 2
def baseEnd_5700762 : Nat := 975743667628843325385893

theorem tailTrace_5700762 : CollatzResearch.WordTrace tailWord_5700762 prefixEnd_5700762 975743667628843325385893 := by
  unfold tailWord_5700762
  simp only [CollatzResearch.WordTrace]
  refine ⟨51980967943280090370362135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138615914515413574320965693 51980967943280090370362135)
  ·
    refine ⟨77971451914920135555543203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51980967943280090370362135 77971451914920135555543203)
    ·
      refine ⟨116957177872380203333314805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77971451914920135555543203 116957177872380203333314805)
      ·
        refine ⟨10964735425535644062498263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 116957177872380203333314805 10964735425535644062498263)
        ·
          refine ⟨16447103138303466093747395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10964735425535644062498263 16447103138303466093747395)
          ·
            refine ⟨24670654707455199140621093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16447103138303466093747395 24670654707455199140621093)
            ·
              refine ⟨4625747757647849838866455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24670654707455199140621093 4625747757647849838866455)
              ·
                refine ⟨6938621636471774758299683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4625747757647849838866455 6938621636471774758299683)
                ·
                  refine ⟨10407932454707662137449525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6938621636471774758299683 10407932454707662137449525)
                  ·
                    refine ⟨975743667628843325385893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10407932454707662137449525 975743667628843325385893)
                    ·
                      rfl

theorem cell23_5700762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 1, 1, 5].length) (baseStart_5700762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5700762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5700762 prefixEnd_5700762 := by exact prefixLift 5700762
  have htrace : WordTrace (prefixWord ++ tailWord_5700762) baseStart_5700762 baseEnd_5700762 := by
    simpa [prefixWord, tailWord_5700762, baseEnd_5700762] using wordTrace_append hprefix tailTrace_5700762
  have hstable : (prefixWord ++ tailWord_5700762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5700762).length < 2 ^ (prefixWord ++ tailWord_5700762).sum := by decide
  have hdescent : baseEnd_5700762 < baseStart_5700762 := by decide
  rcases family_descends (prefixWord ++ tailWord_5700762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5700765 : List Nat := [1, 4, 2, 1, 1, 2, 3, 3, 1, 1, 4]
def baseStart_5700765 : Nat := 118140960795 + 5700765 * 2 ^ 59
def prefixEnd_5700765 : Nat := 4983230072969 + 3 ^ 40 * 5700765 * 2
def baseEnd_5700765 : Nat := 2927232543328493464420165

theorem tailTrace_5700765 : CollatzResearch.WordTrace tailWord_5700765 prefixEnd_5700765 2927232543328493464420165 := by
  unfold tailWord_5700765
  simp only [CollatzResearch.WordTrace]
  refine ⟨207923981192109492993807749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138615987461406328662538499 207923981192109492993807749)
  ·
    refine ⟨38985746473520529936338953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 207923981192109492993807749 38985746473520529936338953)
    ·
      refine ⟨29239309855140397452254215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38985746473520529936338953 29239309855140397452254215)
      ·
        refine ⟨43858964782710596178381323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29239309855140397452254215 43858964782710596178381323)
        ·
          refine ⟨65788447174065894267571985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43858964782710596178381323 65788447174065894267571985)
          ·
            refine ⟨49341335380549420700678989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65788447174065894267571985 49341335380549420700678989)
            ·
              refine ⟨18503000767706032762754621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49341335380549420700678989 18503000767706032762754621)
              ·
                refine ⟨6938625287889762286032983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18503000767706032762754621 6938625287889762286032983)
                ·
                  refine ⟨10407937931834643429049475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6938625287889762286032983 10407937931834643429049475)
                  ·
                    refine ⟨15611906897751965143574213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10407937931834643429049475 15611906897751965143574213)
                    ·
                      refine ⟨2927232543328493464420165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15611906897751965143574213 2927232543328493464420165)
                      ·
                        rfl

theorem cell23_5700765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_5700765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5700765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5700765 prefixEnd_5700765 := by exact prefixLift 5700765
  have htrace : WordTrace (prefixWord ++ tailWord_5700765) baseStart_5700765 baseEnd_5700765 := by
    simpa [prefixWord, tailWord_5700765, baseEnd_5700765] using wordTrace_append hprefix tailTrace_5700765
  have hstable : (prefixWord ++ tailWord_5700765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5700765).length < 2 ^ (prefixWord ++ tailWord_5700765).sum := by decide
  have hdescent : baseEnd_5700765 < baseStart_5700765 := by decide
  rcases family_descends (prefixWord ++ tailWord_5700765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5700768 : List Nat := [2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 5]
def baseStart_5700768 : Nat := 118140960795 + 5700768 * 2 ^ 59
def prefixEnd_5700768 : Nat := 4983230072969 + 3 ^ 40 * 5700768 * 2
def baseEnd_5700768 : Nat := 2927234083770456952682651

theorem tailTrace_5700768 : CollatzResearch.WordTrace tailWord_5700768 prefixEnd_5700768 2927234083770456952682651 := by
  unfold tailWord_5700768
  simp only [CollatzResearch.WordTrace]
  refine ⟨103962045305549312253083479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138616060407399083004111305 103962045305549312253083479)
  ·
    refine ⟨155943067958323968379625219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103962045305549312253083479 155943067958323968379625219)
    ·
      refine ⟨233914601937485952569437829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155943067958323968379625219 233914601937485952569437829)
      ·
        refine ⟨43858987863278616106769593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 233914601937485952569437829 43858987863278616106769593)
        ·
          refine ⟨32894240897458962080077195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43858987863278616106769593 32894240897458962080077195)
          ·
            refine ⟨49341361346188443120115793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32894240897458962080077195 49341361346188443120115793)
            ·
              refine ⟨37006021009641332340086845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49341361346188443120115793 37006021009641332340086845)
              ·
                refine ⟨13877257878615499627532567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37006021009641332340086845 13877257878615499627532567)
                ·
                  refine ⟨20815886817923249441298851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13877257878615499627532567 20815886817923249441298851)
                  ·
                    refine ⟨31223830226884874161948277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20815886817923249441298851 31223830226884874161948277)
                    ·
                      refine ⟨2927234083770456952682651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31223830226884874161948277 2927234083770456952682651)
                      ·
                        rfl

theorem cell23_5700768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_5700768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5700768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5700768 prefixEnd_5700768 := by exact prefixLift 5700768
  have htrace : WordTrace (prefixWord ++ tailWord_5700768) baseStart_5700768 baseEnd_5700768 := by
    simpa [prefixWord, tailWord_5700768, baseEnd_5700768] using wordTrace_append hprefix tailTrace_5700768
  have hstable : (prefixWord ++ tailWord_5700768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5700768).length < 2 ^ (prefixWord ++ tailWord_5700768).sum := by decide
  have hdescent : baseEnd_5700768 < baseStart_5700768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5700768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5700785 : List Nat := [1, 2, 2, 5, 1, 2, 1, 2, 1, 1, 5]
def baseStart_5700785 : Nat := 118140960795 + 5700785 * 2 ^ 59
def prefixEnd_5700785 : Nat := 4983230072969 + 3 ^ 40 * 5700785 * 2
def baseEnd_5700785 : Nat := 2927242812941583386170073

theorem tailTrace_5700785 : CollatzResearch.WordTrace tailWord_5700785 prefixEnd_5700785 2927242812941583386170073 := by
  unfold tailWord_5700785
  simp only [CollatzResearch.WordTrace]
  refine ⟨207924710652037036409535809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138616473768024690939690539 207924710652037036409535809)
  ·
    refine ⟨155943532989027777307151857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207924710652037036409535809 155943532989027777307151857)
    ·
      refine ⟨116957649741770832980363893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155943532989027777307151857 116957649741770832980363893)
      ·
        refine ⟨10964779663291015591909115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 116957649741770832980363893 10964779663291015591909115)
        ·
          refine ⟨16447169494936523387863673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10964779663291015591909115 16447169494936523387863673)
          ·
            refine ⟨12335377121202392540897755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16447169494936523387863673 12335377121202392540897755)
            ·
              refine ⟨18503065681803588811346633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12335377121202392540897755 18503065681803588811346633)
              ·
                refine ⟨13877299261352691608509975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18503065681803588811346633 13877299261352691608509975)
                ·
                  refine ⟨20815948892029037412764963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13877299261352691608509975 20815948892029037412764963)
                  ·
                    refine ⟨31223923338043556119147445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20815948892029037412764963 31223923338043556119147445)
                    ·
                      refine ⟨2927242812941583386170073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31223923338043556119147445 2927242812941583386170073)
                      ·
                        rfl

theorem cell23_5700785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_5700785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5700785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5700785 prefixEnd_5700785 := by exact prefixLift 5700785
  have htrace : WordTrace (prefixWord ++ tailWord_5700785) baseStart_5700785 baseEnd_5700785 := by
    simpa [prefixWord, tailWord_5700785, baseEnd_5700785] using wordTrace_append hprefix tailTrace_5700785
  have hstable : (prefixWord ++ tailWord_5700785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5700785).length < 2 ^ (prefixWord ++ tailWord_5700785).sum := by decide
  have hdescent : baseEnd_5700785 < baseStart_5700785 := by decide
  rcases family_descends (prefixWord ++ tailWord_5700785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5700822 : List Nat := [5, 2, 1, 2, 2, 2, 9]
def baseStart_5700822 : Nat := 118140960795 + 5700822 * 2 ^ 59
def prefixEnd_5700822 : Nat := 4983230072969 + 3 ^ 40 * 5700822 * 2
def baseEnd_5700822 : Nat := 36139034712664194338363

theorem tailTrace_5700822 : CollatzResearch.WordTrace tailWord_5700822 prefixEnd_5700822 36139034712664194338363 := by
  unfold tailWord_5700822
  simp only [CollatzResearch.WordTrace]
  refine ⟨12995378759556436983039545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 138617373435268661152421813 12995378759556436983039545)
  ·
    refine ⟨9746534069667327737279659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12995378759556436983039545 9746534069667327737279659)
    ·
      refine ⟨14619801104500991605919489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9746534069667327737279659 14619801104500991605919489)
      ·
        refine ⟨10964850828375743704439617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14619801104500991605919489 10964850828375743704439617)
        ·
          refine ⟨8223638121281807778329713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10964850828375743704439617 8223638121281807778329713)
          ·
            refine ⟨6167728590961355833747285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8223638121281807778329713 6167728590961355833747285)
            ·
              refine ⟨36139034712664194338363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6167728590961355833747285 36139034712664194338363)
              ·
                rfl

theorem cell23_5700822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 9].length) (baseStart_5700822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5700822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5700822 prefixEnd_5700822 := by exact prefixLift 5700822
  have htrace : WordTrace (prefixWord ++ tailWord_5700822) baseStart_5700822 baseEnd_5700822 := by
    simpa [prefixWord, tailWord_5700822, baseEnd_5700822] using wordTrace_append hprefix tailTrace_5700822
  have hstable : (prefixWord ++ tailWord_5700822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5700822).length < 2 ^ (prefixWord ++ tailWord_5700822).sum := by decide
  have hdescent : baseEnd_5700822 < baseStart_5700822 := by decide
  rcases family_descends (prefixWord ++ tailWord_5700822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5700825 : List Nat := [1, 2, 1, 2, 3, 1, 1, 2, 5, 3, 2]
def baseStart_5700825 : Nat := 118140960795 + 5700825 * 2 ^ 59
def prefixEnd_5700825 : Nat := 4983230072969 + 3 ^ 40 * 5700825 * 2
def baseEnd_5700825 : Nat := 2927263352167763229669889

theorem tailTrace_5700825 : CollatzResearch.WordTrace tailWord_5700825 prefixEnd_5700825 2927263352167763229669889 := by
  unfold tailWord_5700825
  simp only [CollatzResearch.WordTrace]
  refine ⟨207926169571892123240991929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138617446381261415493994619 207926169571892123240991929)
  ·
    refine ⟨155944627178919092430743947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207926169571892123240991929 155944627178919092430743947)
    ·
      refine ⟨233916940768378638646115921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155944627178919092430743947 233916940768378638646115921)
      ·
        refine ⟨175437705576283978984586941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233916940768378638646115921 175437705576283978984586941)
        ·
          refine ⟨65789139591106492119220103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175437705576283978984586941 65789139591106492119220103)
          ·
            refine ⟨98683709386659738178830155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65789139591106492119220103 98683709386659738178830155)
            ·
              refine ⟨148025564079989607268245233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98683709386659738178830155 148025564079989607268245233)
              ·
                refine ⟨111019173059992205451183925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148025564079989607268245233 111019173059992205451183925)
                ·
                  refine ⟨10408047474374269261048493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 111019173059992205451183925 10408047474374269261048493)
                  ·
                    refine ⟨3903017802890350972893185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10408047474374269261048493 3903017802890350972893185)
                    ·
                      refine ⟨2927263352167763229669889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3903017802890350972893185 2927263352167763229669889)
                      ·
                        rfl

theorem cell23_5700825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 5, 3, 2].length) (baseStart_5700825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5700825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5700825 prefixEnd_5700825 := by exact prefixLift 5700825
  have htrace : WordTrace (prefixWord ++ tailWord_5700825) baseStart_5700825 baseEnd_5700825 := by
    simpa [prefixWord, tailWord_5700825, baseEnd_5700825] using wordTrace_append hprefix tailTrace_5700825
  have hstable : (prefixWord ++ tailWord_5700825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5700825).length < 2 ^ (prefixWord ++ tailWord_5700825).sum := by decide
  have hdescent : baseEnd_5700825 < baseStart_5700825 := by decide
  rcases family_descends (prefixWord ++ tailWord_5700825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5700858 : List Nat := [3, 1, 1, 1, 1, 4, 1, 1, 4, 1, 5]
def baseStart_5700858 : Nat := 118140960795 + 5700858 * 2 ^ 59
def prefixEnd_5700858 : Nat := 4983230072969 + 3 ^ 40 * 5700858 * 2
def baseEnd_5700858 : Nat := 2927280297029361600557237

theorem tailTrace_5700858 : CollatzResearch.WordTrace tailWord_5700858 prefixEnd_5700858 2927280297029361600557237 := by
  unfold tailWord_5700858
  simp only [CollatzResearch.WordTrace]
  refine ⟨51981843295193142469235807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138618248787181713251295485 51981843295193142469235807)
  ·
    refine ⟨77972764942789713703853711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51981843295193142469235807 77972764942789713703853711)
    ·
      refine ⟨116959147414184570555780567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77972764942789713703853711 116959147414184570555780567)
      ·
        refine ⟨175438721121276855833670851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116959147414184570555780567 175438721121276855833670851)
        ·
          refine ⟨263158081681915283750506277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175438721121276855833670851 263158081681915283750506277)
          ·
            refine ⟨49342140315359115703219927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 263158081681915283750506277 49342140315359115703219927)
            ·
              refine ⟨74013210473038673554829891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49342140315359115703219927 74013210473038673554829891)
              ·
                refine ⟨111019815709558010332244837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74013210473038673554829891 111019815709558010332244837)
                ·
                  refine ⟨20816215445542126937295907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 111019815709558010332244837 20816215445542126937295907)
                  ·
                    refine ⟨31224323168313190405943861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20816215445542126937295907 31224323168313190405943861)
                    ·
                      refine ⟨2927280297029361600557237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31224323168313190405943861 2927280297029361600557237)
                      ·
                        rfl

theorem cell23_5700858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 4, 1, 5].length) (baseStart_5700858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5700858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5700858 prefixEnd_5700858 := by exact prefixLift 5700858
  have htrace : WordTrace (prefixWord ++ tailWord_5700858) baseStart_5700858 baseEnd_5700858 := by
    simpa [prefixWord, tailWord_5700858, baseEnd_5700858] using wordTrace_append hprefix tailTrace_5700858
  have hstable : (prefixWord ++ tailWord_5700858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5700858).length < 2 ^ (prefixWord ++ tailWord_5700858).sum := by decide
  have hdescent : baseEnd_5700858 < baseStart_5700858 := by decide
  rcases family_descends (prefixWord ++ tailWord_5700858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5700906 : List Nat := [3, 1, 4, 2, 1, 1, 2, 3, 2, 2, 2]
def baseStart_5700906 : Nat := 118140960795 + 5700906 * 2 ^ 59
def prefixEnd_5700906 : Nat := 4983230072969 + 3 ^ 40 * 5700906 * 2
def baseEnd_5700906 : Nat := 2927304944100777412757017

theorem tailTrace_5700906 : CollatzResearch.WordTrace tailWord_5700906 prefixEnd_5700906 2927304944100777412757017 := by
  unfold tailWord_5700906
  simp only [CollatzResearch.WordTrace]
  refine ⟨51982280971149668518672643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138619415923065782716460381 51982280971149668518672643)
  ·
    refine ⟨77973421456724502778008965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51982280971149668518672643 77973421456724502778008965)
    ·
      refine ⟨14620016523135844270876681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77973421456724502778008965 14620016523135844270876681)
      ·
        refine ⟨10965012392351883203157511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14620016523135844270876681 10965012392351883203157511)
        ·
          refine ⟨16447518588527824804736267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10965012392351883203157511 16447518588527824804736267)
          ·
            refine ⟨24671277882791737207104401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16447518588527824804736267 24671277882791737207104401)
            ·
              refine ⟨18503458412093802905328301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24671277882791737207104401 18503458412093802905328301)
              ·
                refine ⟨6938796904535176089498113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18503458412093802905328301 6938796904535176089498113)
                ·
                  refine ⟨5204097678401382067123585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6938796904535176089498113 5204097678401382067123585)
                  ·
                    refine ⟨3903073258801036550342689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5204097678401382067123585 3903073258801036550342689)
                    ·
                      refine ⟨2927304944100777412757017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3903073258801036550342689 2927304944100777412757017)
                      ·
                        rfl

theorem cell23_5700906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_5700906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5700906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5700906 prefixEnd_5700906 := by exact prefixLift 5700906
  have htrace : WordTrace (prefixWord ++ tailWord_5700906) baseStart_5700906 baseEnd_5700906 := by
    simpa [prefixWord, tailWord_5700906, baseEnd_5700906] using wordTrace_append hprefix tailTrace_5700906
  have hstable : (prefixWord ++ tailWord_5700906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5700906).length < 2 ^ (prefixWord ++ tailWord_5700906).sum := by decide
  have hdescent : baseEnd_5700906 < baseStart_5700906 := by decide
  rcases family_descends (prefixWord ++ tailWord_5700906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5700908 : List Nat := [2, 2, 1, 1, 1, 3, 1, 4, 1, 7]
def baseStart_5700908 : Nat := 118140960795 + 5700908 * 2 ^ 59
def prefixEnd_5700908 : Nat := 4983230072969 + 3 ^ 40 * 5700908 * 2
def baseEnd_5700908 : Nat := 975768657020695468310669

theorem tailTrace_5700908 : CollatzResearch.WordTrace tailWord_5700908 prefixEnd_5700908 975768657020695468310669 := by
  unfold tailWord_5700908
  simp only [CollatzResearch.WordTrace]
  refine ⟨103964598415295714208131689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138619464553727618944175585 103964598415295714208131689)
  ·
    refine ⟨77973448811471785656098767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103964598415295714208131689 77973448811471785656098767)
    ·
      refine ⟨116960173217207678484148151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77973448811471785656098767 116960173217207678484148151)
      ·
        refine ⟨175440259825811517726222227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116960173217207678484148151 175440259825811517726222227)
        ·
          refine ⟨263160389738717276589333341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175440259825811517726222227 263160389738717276589333341)
          ·
            refine ⟨98685146152018978721000003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 263160389738717276589333341 98685146152018978721000003)
            ·
              refine ⟨148027719228028468081500005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98685146152018978721000003 148027719228028468081500005)
              ·
                refine ⟨27755197355255337765281251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 148027719228028468081500005 27755197355255337765281251)
                ·
                  refine ⟨41632796032883006647921877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27755197355255337765281251 41632796032883006647921877)
                  ·
                    refine ⟨975768657020695468310669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41632796032883006647921877 975768657020695468310669)
                    ·
                      rfl

theorem cell23_5700908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 7].length) (baseStart_5700908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5700908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5700908 prefixEnd_5700908 := by exact prefixLift 5700908
  have htrace : WordTrace (prefixWord ++ tailWord_5700908) baseStart_5700908 baseEnd_5700908 := by
    simpa [prefixWord, tailWord_5700908, baseEnd_5700908] using wordTrace_append hprefix tailTrace_5700908
  have hstable : (prefixWord ++ tailWord_5700908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5700908).length < 2 ^ (prefixWord ++ tailWord_5700908).sum := by decide
  have hdescent : baseEnd_5700908 < baseStart_5700908 := by decide
  rcases family_descends (prefixWord ++ tailWord_5700908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5700929 : List Nat := [1, 2, 5, 2, 1, 2, 2, 3, 5]
def baseStart_5700929 : Nat := 118140960795 + 5700929 * 2 ^ 59
def prefixEnd_5700929 : Nat := 4983230072969 + 3 ^ 40 * 5700929 * 2
def baseEnd_5700929 : Nat := 325257417128425646974379

theorem tailTrace_5700929 : CollatzResearch.WordTrace tailWord_5700929 prefixEnd_5700929 325257417128425646974379 := by
  unfold tailWord_5700929
  simp only [CollatzResearch.WordTrace]
  refine ⟨207929962763515349002777841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138619975175676899335185227 207929962763515349002777841)
  ·
    refine ⟨155947472072636511752083381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207929962763515349002777841 155947472072636511752083381)
    ·
      refine ⟨14620075506809672976757817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 155947472072636511752083381 14620075506809672976757817)
      ·
        refine ⟨10965056630107254732568363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14620075506809672976757817 10965056630107254732568363)
        ·
          refine ⟨16447584945160882098852545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10965056630107254732568363 16447584945160882098852545)
          ·
            refine ⟨12335688708870661574139409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16447584945160882098852545 12335688708870661574139409)
            ·
              refine ⟨9251766531652996180604557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12335688708870661574139409 9251766531652996180604557)
              ·
                refine ⟨3469412449369873567726709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9251766531652996180604557 3469412449369873567726709)
                ·
                  refine ⟨325257417128425646974379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3469412449369873567726709 325257417128425646974379)
                  ·
                    rfl

theorem cell23_5700929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 3, 5].length) (baseStart_5700929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5700929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5700929 prefixEnd_5700929 := by exact prefixLift 5700929
  have htrace : WordTrace (prefixWord ++ tailWord_5700929) baseStart_5700929 baseEnd_5700929 := by
    simpa [prefixWord, tailWord_5700929, baseEnd_5700929] using wordTrace_append hprefix tailTrace_5700929
  have hstable : (prefixWord ++ tailWord_5700929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5700929).length < 2 ^ (prefixWord ++ tailWord_5700929).sum := by decide
  have hdescent : baseEnd_5700929 < baseStart_5700929 := by decide
  rcases family_descends (prefixWord ++ tailWord_5700929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5700938 : List Nat := [3, 1, 2, 1, 1, 1, 1, 2, 1, 10]
def baseStart_5700938 : Nat := 118140960795 + 5700938 * 2 ^ 59
def prefixEnd_5700938 : Nat := 4983230072969 + 3 ^ 40 * 5700938 * 2
def baseEnd_5700938 : Nat := 975773791827240429185623

theorem tailTrace_5700938 : CollatzResearch.WordTrace tailWord_5700938 prefixEnd_5700938 975773791827240429185623 := by
  unfold tailWord_5700938
  simp only [CollatzResearch.WordTrace]
  refine ⟨51982572755120685884963867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138620194013655162359903645 51982572755120685884963867)
  ·
    refine ⟨77973859132681028827445801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51982572755120685884963867 77973859132681028827445801)
    ·
      refine ⟨58480394349510771620584351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77973859132681028827445801 58480394349510771620584351)
      ·
        refine ⟨87720591524266157430876527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58480394349510771620584351 87720591524266157430876527)
        ·
          refine ⟨131580887286399236146314791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87720591524266157430876527 131580887286399236146314791)
          ·
            refine ⟨197371330929598854219472187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131580887286399236146314791 197371330929598854219472187)
            ·
              refine ⟨296056996394398281329208281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197371330929598854219472187 296056996394398281329208281)
              ·
                refine ⟨222042747295798710996906211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 296056996394398281329208281 222042747295798710996906211)
                ·
                  refine ⟨333064120943698066495359317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 222042747295798710996906211 333064120943698066495359317)
                  ·
                    refine ⟨975773791827240429185623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 333064120943698066495359317 975773791827240429185623)
                    ·
                      rfl

theorem cell23_5700938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 1, 10].length) (baseStart_5700938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5700938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5700938 prefixEnd_5700938 := by exact prefixLift 5700938
  have htrace : WordTrace (prefixWord ++ tailWord_5700938) baseStart_5700938 baseEnd_5700938 := by
    simpa [prefixWord, tailWord_5700938, baseEnd_5700938] using wordTrace_append hprefix tailTrace_5700938
  have hstable : (prefixWord ++ tailWord_5700938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5700938).length < 2 ^ (prefixWord ++ tailWord_5700938).sum := by decide
  have hdescent : baseEnd_5700938 < baseStart_5700938 := by decide
  rcases family_descends (prefixWord ++ tailWord_5700938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5700945 : List Nat := [1, 2, 2, 1, 4, 1, 2, 1, 4, 1, 4]
def baseStart_5700945 : Nat := 118140960795 + 5700945 * 2 ^ 59
def prefixEnd_5700945 : Nat := 4983230072969 + 3 ^ 40 * 5700945 * 2
def baseEnd_5700945 : Nat := 2927324969846302760169337

theorem tailTrace_5700945 : CollatzResearch.WordTrace tailWord_5700945 prefixEnd_5700945 2927324969846302760169337 := by
  unfold tailWord_5700945
  simp only [CollatzResearch.WordTrace]
  refine ⟨207930546331457383735360289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138620364220971589156906859 207930546331457383735360289)
  ·
    refine ⟨155947909748593037801520217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207930546331457383735360289 155947909748593037801520217)
    ·
      refine ⟨116960932311444778351140163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155947909748593037801520217 116960932311444778351140163)
      ·
        refine ⟨175441398467167167526710245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116960932311444778351140163 175441398467167167526710245)
        ·
          refine ⟨32895262212593843911258171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 175441398467167167526710245 32895262212593843911258171)
          ·
            refine ⟨49342893318890765866887257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32895262212593843911258171 49342893318890765866887257)
            ·
              refine ⟨37007169989168074400165443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49342893318890765866887257 37007169989168074400165443)
              ·
                refine ⟨55510754983752111600248165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37007169989168074400165443 55510754983752111600248165)
                ·
                  refine ⟨10408266559453520925046531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55510754983752111600248165 10408266559453520925046531)
                  ·
                    refine ⟨15612399839180281387569797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10408266559453520925046531 15612399839180281387569797)
                    ·
                      refine ⟨2927324969846302760169337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15612399839180281387569797 2927324969846302760169337)
                      ·
                        rfl

theorem cell23_5700945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 4, 1, 4].length) (baseStart_5700945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5700945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5700945 prefixEnd_5700945 := by exact prefixLift 5700945
  have htrace : WordTrace (prefixWord ++ tailWord_5700945) baseStart_5700945 baseEnd_5700945 := by
    simpa [prefixWord, tailWord_5700945, baseEnd_5700945] using wordTrace_append hprefix tailTrace_5700945
  have hstable : (prefixWord ++ tailWord_5700945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5700945).length < 2 ^ (prefixWord ++ tailWord_5700945).sum := by decide
  have hdescent : baseEnd_5700945 < baseStart_5700945 := by decide
  rcases family_descends (prefixWord ++ tailWord_5700945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5700957 : List Nat := [1, 4, 5, 1, 1, 1, 3, 1, 2, 2, 2]
def baseStart_5700957 : Nat := 118140960795 + 5700957 * 2 ^ 59
def prefixEnd_5700957 : Nat := 4983230072969 + 3 ^ 40 * 5700957 * 2
def baseEnd_5700957 : Nat := 2927331131614156713219283

theorem tailTrace_5700957 : CollatzResearch.WordTrace tailWord_5700957 prefixEnd_5700957 2927331131614156713219283 := by
  unfold tailWord_5700957
  simp only [CollatzResearch.WordTrace]
  refine ⟨207930984007413909784797125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138620656004942606523198083 207930984007413909784797125)
  ·
    refine ⟨38987059501390108084649461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 207930984007413909784797125 38987059501390108084649461)
    ·
      refine ⟨3655036828255322632935887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38987059501390108084649461 3655036828255322632935887)
      ·
        refine ⟨5482555242382983949403831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3655036828255322632935887 5482555242382983949403831)
        ·
          refine ⟨8223832863574475924105747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5482555242382983949403831 8223832863574475924105747)
          ·
            refine ⟨12335749295361713886158621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8223832863574475924105747 12335749295361713886158621)
            ·
              refine ⟨4625905985760642707309483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12335749295361713886158621 4625905985760642707309483)
              ·
                refine ⟨6938858978640964060964225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4625905985760642707309483 6938858978640964060964225)
                ·
                  refine ⟨5204144233980723045723169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6938858978640964060964225 5204144233980723045723169)
                  ·
                    refine ⟨3903108175485542284292377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5204144233980723045723169 3903108175485542284292377)
                    ·
                      refine ⟨2927331131614156713219283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3903108175485542284292377 2927331131614156713219283)
                      ·
                        rfl

theorem cell23_5700957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_5700957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5700957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5700957 prefixEnd_5700957 := by exact prefixLift 5700957
  have htrace : WordTrace (prefixWord ++ tailWord_5700957) baseStart_5700957 baseEnd_5700957 := by
    simpa [prefixWord, tailWord_5700957, baseEnd_5700957] using wordTrace_append hprefix tailTrace_5700957
  have hstable : (prefixWord ++ tailWord_5700957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5700957).length < 2 ^ (prefixWord ++ tailWord_5700957).sum := by decide
  have hdescent : baseEnd_5700957 < baseStart_5700957 := by decide
  rcases family_descends (prefixWord ++ tailWord_5700957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5700965 : List Nat := [1, 3, 1, 3, 1, 2, 1, 1, 3, 4, 3]
def baseStart_5700965 : Nat := 118140960795 + 5700965 * 2 ^ 59
def prefixEnd_5700965 : Nat := 4983230072969 + 3 ^ 40 * 5700965 * 2
def baseEnd_5700965 : Nat := 2927335239459392681919245

theorem tailTrace_5700965 : CollatzResearch.WordTrace tailWord_5700965 prefixEnd_5700965 2927335239459392681919245 := by
  unfold tailWord_5700965
  simp only [CollatzResearch.WordTrace]
  refine ⟨207931275791384927151088349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138620850527589951434058899 207931275791384927151088349)
  ·
    refine ⟨77974228421769347681658131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207931275791384927151088349 77974228421769347681658131)
    ·
      refine ⟨116961342632654021522487197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77974228421769347681658131 116961342632654021522487197)
      ·
        refine ⟨43860503487245258070932699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116961342632654021522487197 43860503487245258070932699)
        ·
          refine ⟨65790755230867887106399049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43860503487245258070932699 65790755230867887106399049)
          ·
            refine ⟨49343066423150915329799287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65790755230867887106399049 49343066423150915329799287)
            ·
              refine ⟨74014599634726372994698931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49343066423150915329799287 74014599634726372994698931)
              ·
                refine ⟨111021899452089559492048397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74014599634726372994698931 111021899452089559492048397)
                ·
                  refine ⟨41633212294533584809518149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111021899452089559492048397 41633212294533584809518149)
                  ·
                    refine ⟨7806227305225047151784653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41633212294533584809518149 7806227305225047151784653)
                    ·
                      refine ⟨2927335239459392681919245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7806227305225047151784653 2927335239459392681919245)
                      ·
                        rfl

theorem cell23_5700965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_5700965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5700965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5700965 prefixEnd_5700965 := by exact prefixLift 5700965
  have htrace : WordTrace (prefixWord ++ tailWord_5700965) baseStart_5700965 baseEnd_5700965 := by
    simpa [prefixWord, tailWord_5700965, baseEnd_5700965] using wordTrace_append hprefix tailTrace_5700965
  have hstable : (prefixWord ++ tailWord_5700965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5700965).length < 2 ^ (prefixWord ++ tailWord_5700965).sum := by decide
  have hdescent : baseEnd_5700965 < baseStart_5700965 := by decide
  rcases family_descends (prefixWord ++ tailWord_5700965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5700972 : List Nat := [2, 2, 1, 1, 5, 1, 2, 2, 3, 4]
def baseStart_5700972 : Nat := 118140960795 + 5700972 * 2 ^ 59
def prefixEnd_5700972 : Nat := 4983230072969 + 3 ^ 40 * 5700972 * 2
def baseEnd_5700972 : Nat := 975779611274658051510571

theorem tailTrace_5700972 : CollatzResearch.WordTrace tailWord_5700972 prefixEnd_5700972 975779611274658051510571 := by
  unfold tailWord_5700972
  simp only [CollatzResearch.WordTrace]
  refine ⟨103965765551179783673296585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138621020734906378231062113 103965765551179783673296585)
  ·
    refine ⟨77974324163384837754972439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103965765551179783673296585 77974324163384837754972439)
    ·
      refine ⟨116961486245077256632458659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77974324163384837754972439 116961486245077256632458659)
      ·
        refine ⟨175442229367615884948687989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116961486245077256632458659 175442229367615884948687989)
        ·
          refine ⟨16447709003213989213939499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 175442229367615884948687989 16447709003213989213939499)
          ·
            refine ⟨24671563504820983820909249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16447709003213989213939499 24671563504820983820909249)
            ·
              refine ⟨18503672628615737865681937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24671563504820983820909249 18503672628615737865681937)
              ·
                refine ⟨13877754471461803399261453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18503672628615737865681937 13877754471461803399261453)
                ·
                  refine ⟨5204157926798176274723045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13877754471461803399261453 5204157926798176274723045)
                  ·
                    refine ⟨975779611274658051510571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5204157926798176274723045 975779611274658051510571)
                    ·
                      rfl

theorem cell23_5700972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 4].length) (baseStart_5700972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5700972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5700972 prefixEnd_5700972 := by exact prefixLift 5700972
  have htrace : WordTrace (prefixWord ++ tailWord_5700972) baseStart_5700972 baseEnd_5700972 := by
    simpa [prefixWord, tailWord_5700972, baseEnd_5700972] using wordTrace_append hprefix tailTrace_5700972
  have hstable : (prefixWord ++ tailWord_5700972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5700972).length < 2 ^ (prefixWord ++ tailWord_5700972).sum := by decide
  have hdescent : baseEnd_5700972 < baseStart_5700972 := by decide
  rcases family_descends (prefixWord ++ tailWord_5700972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5701006 : List Nat := [4, 1, 1, 4, 2, 2, 1, 1, 3, 4]
def baseStart_5701006 : Nat := 118140960795 + 5701006 * 2 ^ 59
def prefixEnd_5701006 : Nat := 4983230072969 + 3 ^ 40 * 5701006 * 2
def baseEnd_5701006 : Nat := 975785430722075673835519

theorem tailTrace_5701006 : CollatzResearch.WordTrace tailWord_5701006 prefixEnd_5701006 975785430722075673835519 := by
  unfold tailWord_5701006
  simp only [CollatzResearch.WordTrace]
  refine ⟨25991596398029548894166359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138621847456157594102220581 25991596398029548894166359)
  ·
    refine ⟨38987394597044323341249539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25991596398029548894166359 38987394597044323341249539)
    ·
      refine ⟨58481091895566485011874309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38987394597044323341249539 58481091895566485011874309)
      ·
        refine ⟨10965204730418715939726433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58481091895566485011874309 10965204730418715939726433)
        ·
          refine ⟨8223903547814036954794825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10965204730418715939726433 8223903547814036954794825)
          ·
            refine ⟨6167927660860527716096119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8223903547814036954794825 6167927660860527716096119)
            ·
              refine ⟨9251891491290791574144179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6167927660860527716096119 9251891491290791574144179)
              ·
                refine ⟨13877837236936187361216269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9251891491290791574144179 13877837236936187361216269)
                ·
                  refine ⟨5204188963851070260456101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13877837236936187361216269 5204188963851070260456101)
                  ·
                    refine ⟨975785430722075673835519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5204188963851070260456101 975785430722075673835519)
                    ·
                      rfl

theorem cell23_5701006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 1, 3, 4].length) (baseStart_5701006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5701006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5701006 prefixEnd_5701006 := by exact prefixLift 5701006
  have htrace : WordTrace (prefixWord ++ tailWord_5701006) baseStart_5701006 baseEnd_5701006 := by
    simpa [prefixWord, tailWord_5701006, baseEnd_5701006] using wordTrace_append hprefix tailTrace_5701006
  have hstable : (prefixWord ++ tailWord_5701006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5701006).length < 2 ^ (prefixWord ++ tailWord_5701006).sum := by decide
  have hdescent : baseEnd_5701006 < baseStart_5701006 := by decide
  rcases family_descends (prefixWord ++ tailWord_5701006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5701015 : List Nat := [1, 1, 3, 3, 1, 1, 1, 4, 3, 5]
def baseStart_5701015 : Nat := 118140960795 + 5701015 * 2 ^ 59
def prefixEnd_5701015 : Nat := 4983230072969 + 3 ^ 40 * 5701015 * 2
def baseEnd_5701015 : Nat := 975786971164039162098005

theorem tailTrace_5701015 : CollatzResearch.WordTrace tailWord_5701015 prefixEnd_5701015 975786971164039162098005 := by
  unfold tailWord_5701015
  simp only [CollatzResearch.WordTrace]
  refine ⟨207933099441203785690408499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138622066294135857126938999 207933099441203785690408499)
  ·
    refine ⟨311899649161805678535612749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207933099441203785690408499 311899649161805678535612749)
    ·
      refine ⟨116962368435677129450854781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 311899649161805678535612749 116962368435677129450854781)
      ·
        refine ⟨43860888163378923544070543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116962368435677129450854781 43860888163378923544070543)
        ·
          refine ⟨65791332245068385316105815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43860888163378923544070543 65791332245068385316105815)
          ·
            refine ⟨98686998367602577974158723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65791332245068385316105815 98686998367602577974158723)
            ·
              refine ⟨148030497551403866961238085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98686998367602577974158723 148030497551403866961238085)
              ·
                refine ⟨27755718290888225055232141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 148030497551403866961238085 27755718290888225055232141)
                ·
                  refine ⟨10408394359083084395712053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27755718290888225055232141 10408394359083084395712053)
                  ·
                    refine ⟨975786971164039162098005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10408394359083084395712053 975786971164039162098005)
                    ·
                      rfl

theorem cell23_5701015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 3, 5].length) (baseStart_5701015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5701015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5701015 prefixEnd_5701015 := by exact prefixLift 5701015
  have htrace : WordTrace (prefixWord ++ tailWord_5701015) baseStart_5701015 baseEnd_5701015 := by
    simpa [prefixWord, tailWord_5701015, baseEnd_5701015] using wordTrace_append hprefix tailTrace_5701015
  have hstable : (prefixWord ++ tailWord_5701015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5701015).length < 2 ^ (prefixWord ++ tailWord_5701015).sum := by decide
  have hdescent : baseEnd_5701015 < baseStart_5701015 := by decide
  rcases family_descends (prefixWord ++ tailWord_5701015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5701065 : List Nat := [1, 2, 1, 1, 2, 1, 3, 1, 5, 2, 4]
def baseStart_5701065 : Nat := 118140960795 + 5701065 * 2 ^ 59
def prefixEnd_5701065 : Nat := 4983230072969 + 3 ^ 40 * 5701065 * 2
def baseEnd_5701065 : Nat := 2927386587524842290668785

theorem tailTrace_5701065 : CollatzResearch.WordTrace tailWord_5701065 prefixEnd_5701065 2927386587524842290668785 := by
  unfold tailWord_5701065
  simp only [CollatzResearch.WordTrace]
  refine ⟨207934923091022644229728649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138623282060681762819819099 207934923091022644229728649)
  ·
    refine ⟨155951192318266983172296487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207934923091022644229728649 155951192318266983172296487)
    ·
      refine ⟨233926788477400474758444731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155951192318266983172296487 233926788477400474758444731)
      ·
        refine ⟨350890182716100712137667097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233926788477400474758444731 350890182716100712137667097)
        ·
          refine ⟨263167637037075534103250323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 350890182716100712137667097 263167637037075534103250323)
          ·
            refine ⟨394751455555613301154875485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263167637037075534103250323 394751455555613301154875485)
            ·
              refine ⟨148031795833354987933078307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 394751455555613301154875485 148031795833354987933078307)
              ·
                refine ⟨222047693750032481899617461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148031795833354987933078307 222047693750032481899617461)
                ·
                  refine ⟨20816971289065545178089137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 222047693750032481899617461 20816971289065545178089137)
                  ·
                    refine ⟨15612728466799158883566853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20816971289065545178089137 15612728466799158883566853)
                    ·
                      refine ⟨2927386587524842290668785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15612728466799158883566853 2927386587524842290668785)
                      ·
                        rfl

theorem cell23_5701065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5, 2, 4].length) (baseStart_5701065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5701065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5701065 prefixEnd_5701065 := by exact prefixLift 5701065
  have htrace : WordTrace (prefixWord ++ tailWord_5701065) baseStart_5701065 baseEnd_5701065 := by
    simpa [prefixWord, tailWord_5701065, baseEnd_5701065] using wordTrace_append hprefix tailTrace_5701065
  have hstable : (prefixWord ++ tailWord_5701065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5701065).length < 2 ^ (prefixWord ++ tailWord_5701065).sum := by decide
  have hdescent : baseEnd_5701065 < baseStart_5701065 := by decide
  rcases family_descends (prefixWord ++ tailWord_5701065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5701082 : List Nat := [3, 1, 1, 2, 3, 2, 1, 3, 1, 2, 4]
def baseStart_5701082 : Nat := 118140960795 + 5701082 * 2 ^ 59
def prefixEnd_5701082 : Nat := 4983230072969 + 3 ^ 40 * 5701082 * 2
def baseEnd_5701082 : Nat := 2927395316695968724156207

theorem tailTrace_5701082 : CollatzResearch.WordTrace tailWord_5701082 prefixEnd_5701082 2927395316695968724156207 := by
  unfold tailWord_5701082
  simp only [CollatzResearch.WordTrace]
  refine ⟨51983885782990264033274375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138623695421307370755398333 51983885782990264033274375)
  ·
    refine ⟨77975828674485396049911563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51983885782990264033274375 77975828674485396049911563)
    ·
      refine ⟨116963743011728094074867345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77975828674485396049911563 116963743011728094074867345)
      ·
        refine ⟨87722807258796070556150509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116963743011728094074867345 87722807258796070556150509)
        ·
          refine ⟨32896052722048526458556441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87722807258796070556150509 32896052722048526458556441)
          ·
            refine ⟨24672039541536394843917331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32896052722048526458556441 24672039541536394843917331)
            ·
              refine ⟨37008059312304592265875997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24672039541536394843917331 37008059312304592265875997)
              ·
                refine ⟨13878022242114222099703499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37008059312304592265875997 13878022242114222099703499)
                ·
                  refine ⟨20817033363171333149555249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13878022242114222099703499 20817033363171333149555249)
                  ·
                    refine ⟨15612775022378499862166437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20817033363171333149555249 15612775022378499862166437)
                    ·
                      refine ⟨2927395316695968724156207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15612775022378499862166437 2927395316695968724156207)
                      ·
                        rfl

theorem cell23_5701082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3, 1, 2, 4].length) (baseStart_5701082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5701082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5701082 prefixEnd_5701082 := by exact prefixLift 5701082
  have htrace : WordTrace (prefixWord ++ tailWord_5701082) baseStart_5701082 baseEnd_5701082 := by
    simpa [prefixWord, tailWord_5701082, baseEnd_5701082] using wordTrace_append hprefix tailTrace_5701082
  have hstable : (prefixWord ++ tailWord_5701082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5701082).length < 2 ^ (prefixWord ++ tailWord_5701082).sum := by decide
  have hdescent : baseEnd_5701082 < baseStart_5701082 := by decide
  rcases family_descends (prefixWord ++ tailWord_5701082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5701106 : List Nat := [3, 2, 1, 4, 1, 2, 1, 3, 1, 2, 3]
def baseStart_5701106 : Nat := 118140960795 + 5701106 * 2 ^ 59
def prefixEnd_5701106 : Nat := 4983230072969 + 3 ^ 40 * 5701106 * 2
def baseEnd_5701106 : Nat := 2927407640231676630256097

theorem tailTrace_5701106 : CollatzResearch.WordTrace tailWord_5701106 prefixEnd_5701106 2927407640231676630256097 := by
  unfold tailWord_5701106
  simp only [CollatzResearch.WordTrace]
  refine ⟨51984104620968527057992793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138624278989249405487980781 51984104620968527057992793)
  ·
    refine ⟨38988078465726395293494595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51984104620968527057992793 38988078465726395293494595)
    ·
      refine ⟨58482117698589592940241893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38988078465726395293494595 58482117698589592940241893)
      ·
        refine ⟨10965397068485548676295355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58482117698589592940241893 10965397068485548676295355)
        ·
          refine ⟨16448095602728323014443033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10965397068485548676295355 16448095602728323014443033)
          ·
            refine ⟨12336071702046242260832275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16448095602728323014443033 12336071702046242260832275)
            ·
              refine ⟨18504107553069363391248413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12336071702046242260832275 18504107553069363391248413)
              ·
                refine ⟨6939040332401011271718155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18504107553069363391248413 6939040332401011271718155)
                ·
                  refine ⟨10408560498601516907577233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6939040332401011271718155 10408560498601516907577233)
                  ·
                    refine ⟨7806420373951137680682925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10408560498601516907577233 7806420373951137680682925)
                    ·
                      refine ⟨2927407640231676630256097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7806420373951137680682925 2927407640231676630256097)
                      ·
                        rfl

theorem cell23_5701106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_5701106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5701106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5701106 prefixEnd_5701106 := by exact prefixLift 5701106
  have htrace : WordTrace (prefixWord ++ tailWord_5701106) baseStart_5701106 baseEnd_5701106 := by
    simpa [prefixWord, tailWord_5701106, baseEnd_5701106] using wordTrace_append hprefix tailTrace_5701106
  have hstable : (prefixWord ++ tailWord_5701106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5701106).length < 2 ^ (prefixWord ++ tailWord_5701106).sum := by decide
  have hdescent : baseEnd_5701106 < baseStart_5701106 := by decide
  rcases family_descends (prefixWord ++ tailWord_5701106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5701115 : List Nat := [1, 1, 1, 1, 1, 3, 2, 4, 2, 2, 5]
def baseStart_5701115 : Nat := 118140960795 + 5701115 * 2 ^ 59
def prefixEnd_5701115 : Nat := 4983230072969 + 3 ^ 40 * 5701115 * 2
def baseEnd_5701115 : Nat := 2927412261557567095043555

theorem tailTrace_5701115 : CollatzResearch.WordTrace tailWord_5701115 prefixEnd_5701115 2927412261557567095043555 := by
  unfold tailWord_5701115
  simp only [CollatzResearch.WordTrace]
  refine ⟨207936746740841502769048799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138624497827227668512699199 207936746740841502769048799)
  ·
    refine ⟨311905120111262254153573199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207936746740841502769048799 311905120111262254153573199)
    ·
      refine ⟨467857680166893381230359799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311905120111262254153573199 467857680166893381230359799)
      ·
        refine ⟨701786520250340071845539699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 467857680166893381230359799 701786520250340071845539699)
        ·
          refine ⟨1052679780375510107768309549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 701786520250340071845539699 1052679780375510107768309549)
          ·
            refine ⟨394754917640816290413116081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1052679780375510107768309549 394754917640816290413116081)
            ·
              refine ⟨296066188230612217809837061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 394754917640816290413116081 296066188230612217809837061)
              ·
                refine ⟨55512410293239790839344449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 296066188230612217809837061 55512410293239790839344449)
                ·
                  refine ⟨41634307719929843129508337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55512410293239790839344449 41634307719929843129508337)
                  ·
                    refine ⟨31225730789947382347131253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41634307719929843129508337 31225730789947382347131253)
                    ·
                      refine ⟨2927412261557567095043555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31225730789947382347131253 2927412261557567095043555)
                      ·
                        rfl

theorem cell23_5701115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2, 5].length) (baseStart_5701115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5701115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5701115 prefixEnd_5701115 := by exact prefixLift 5701115
  have htrace : WordTrace (prefixWord ++ tailWord_5701115) baseStart_5701115 baseEnd_5701115 := by
    simpa [prefixWord, tailWord_5701115, baseEnd_5701115] using wordTrace_append hprefix tailTrace_5701115
  have hstable : (prefixWord ++ tailWord_5701115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5701115).length < 2 ^ (prefixWord ++ tailWord_5701115).sum := by decide
  have hdescent : baseEnd_5701115 < baseStart_5701115 := by decide
  rcases family_descends (prefixWord ++ tailWord_5701115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5701119 : List Nat := [1, 1, 2, 2, 1, 2, 2, 6, 2, 1, 3]
def baseStart_5701119 : Nat := 118140960795 + 5701119 * 2 ^ 59
def prefixEnd_5701119 : Nat := 4983230072969 + 3 ^ 40 * 5701119 * 2
def baseEnd_5701119 : Nat := 2927414315480185079393537

theorem tailTrace_5701119 : CollatzResearch.WordTrace tailWord_5701119 prefixEnd_5701119 2927414315480185079393537 := by
  unfold tailWord_5701119
  simp only [CollatzResearch.WordTrace]
  refine ⟨207936892632827011452194411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138624595088551340968129607 207936892632827011452194411)
  ·
    refine ⟨311905338949240517178291617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207936892632827011452194411 311905338949240517178291617)
    ·
      refine ⟨233929004211930387883718713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311905338949240517178291617 233929004211930387883718713)
      ·
        refine ⟨175446753158947790912789035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233929004211930387883718713 175446753158947790912789035)
        ·
          refine ⟨263170129738421686369183553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175446753158947790912789035 263170129738421686369183553)
          ·
            refine ⟨197377597303816264776887665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 263170129738421686369183553 197377597303816264776887665)
            ·
              refine ⟨148033197977862198582665749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197377597303816264776887665 148033197977862198582665749)
              ·
                refine ⟨6939056155212290558562457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 148033197977862198582665749 6939056155212290558562457)
                ·
                  refine ⟨5204292116409217918921843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6939056155212290558562457 5204292116409217918921843)
                  ·
                    refine ⟨7806438174613826878382765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5204292116409217918921843 7806438174613826878382765)
                    ·
                      refine ⟨2927414315480185079393537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7806438174613826878382765 2927414315480185079393537)
                      ·
                        rfl

theorem cell23_5701119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 6, 2, 1, 3].length) (baseStart_5701119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5701119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5701119 prefixEnd_5701119 := by exact prefixLift 5701119
  have htrace : WordTrace (prefixWord ++ tailWord_5701119) baseStart_5701119 baseEnd_5701119 := by
    simpa [prefixWord, tailWord_5701119, baseEnd_5701119] using wordTrace_append hprefix tailTrace_5701119
  have hstable : (prefixWord ++ tailWord_5701119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5701119).length < 2 ^ (prefixWord ++ tailWord_5701119).sum := by decide
  have hdescent : baseEnd_5701119 < baseStart_5701119 := by decide
  rcases family_descends (prefixWord ++ tailWord_5701119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5701135 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 6, 6]
def baseStart_5701135 : Nat := 118140960795 + 5701135 * 2 ^ 59
def prefixEnd_5701135 : Nat := 4983230072969 + 3 ^ 40 * 5701135 * 2
def baseEnd_5701135 : Nat := 975807510390219005597821

theorem tailTrace_5701135 : CollatzResearch.WordTrace tailWord_5701135 prefixEnd_5701135 975807510390219005597821 := by
  unfold tailWord_5701135
  simp only [CollatzResearch.WordTrace]
  refine ⟨207937476200769046184776859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138624984133846030789851239 207937476200769046184776859)
  ·
    refine ⟨311906214301153569277165289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207937476200769046184776859 311906214301153569277165289)
    ·
      refine ⟨233929660725865176957873967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311906214301153569277165289 233929660725865176957873967)
      ·
        refine ⟨350894491088797765436810951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233929660725865176957873967 350894491088797765436810951)
        ·
          refine ⟨526341736633196648155216427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350894491088797765436810951 526341736633196648155216427)
          ·
            refine ⟨789512604949794972232824641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 526341736633196648155216427 789512604949794972232824641)
            ·
              refine ⟨592134453712346229174618481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 789512604949794972232824641 592134453712346229174618481)
              ·
                refine ⟨444100840284259671880963861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 592134453712346229174618481 444100840284259671880963861)
                ·
                  refine ⟨20817226888324672119420181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 444100840284259671880963861 20817226888324672119420181)
                  ·
                    refine ⟨975807510390219005597821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20817226888324672119420181 975807510390219005597821)
                    ·
                      rfl

theorem cell23_5701135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6, 6].length) (baseStart_5701135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5701135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5701135 prefixEnd_5701135 := by exact prefixLift 5701135
  have htrace : WordTrace (prefixWord ++ tailWord_5701135) baseStart_5701135 baseEnd_5701135 := by
    simpa [prefixWord, tailWord_5701135, baseEnd_5701135] using wordTrace_append hprefix tailTrace_5701135
  have hstable : (prefixWord ++ tailWord_5701135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5701135).length < 2 ^ (prefixWord ++ tailWord_5701135).sum := by decide
  have hdescent : baseEnd_5701135 < baseStart_5701135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5701135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5701176 : List Nat := [2, 1, 2, 1, 4, 2, 2, 1, 4, 2, 2]
def baseStart_5701176 : Nat := 118140960795 + 5701176 * 2 ^ 59
def prefixEnd_5701176 : Nat := 4983230072969 + 3 ^ 40 * 5701176 * 2
def baseEnd_5701176 : Nat := 2927443583877491356380775

theorem tailTrace_5701176 : CollatzResearch.WordTrace tailWord_5701176 prefixEnd_5701176 2927443583877491356380775 := by
  unfold tailWord_5701176
  simp only [CollatzResearch.WordTrace]
  refine ⟨103969485796810255093509691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138625981062413673458012921 103969485796810255093509691)
  ·
    refine ⟨155954228695215382640264537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103969485796810255093509691 155954228695215382640264537)
    ·
      refine ⟨116965671521411536980198403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155954228695215382640264537 116965671521411536980198403)
      ·
        refine ⟨175448507282117305470297605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116965671521411536980198403 175448507282117305470297605)
        ·
          refine ⟨32896595115396994775680801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 175448507282117305470297605 32896595115396994775680801)
          ·
            refine ⟨24672446336547746081760601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32896595115396994775680801 24672446336547746081760601)
            ·
              refine ⟨18504334752410809561320451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24672446336547746081760601 18504334752410809561320451)
              ·
                refine ⟨27756502128616214341980677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18504334752410809561320451 27756502128616214341980677)
                ·
                  refine ⟨5204344149115540189121377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27756502128616214341980677 5204344149115540189121377)
                  ·
                    refine ⟨3903258111836655141841033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5204344149115540189121377 3903258111836655141841033)
                    ·
                      refine ⟨2927443583877491356380775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3903258111836655141841033 2927443583877491356380775)
                      ·
                        rfl

theorem cell23_5701176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 4, 2, 2].length) (baseStart_5701176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5701176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5701176 prefixEnd_5701176 := by exact prefixLift 5701176
  have htrace : WordTrace (prefixWord ++ tailWord_5701176) baseStart_5701176 baseEnd_5701176 := by
    simpa [prefixWord, tailWord_5701176, baseEnd_5701176] using wordTrace_append hprefix tailTrace_5701176
  have hstable : (prefixWord ++ tailWord_5701176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5701176).length < 2 ^ (prefixWord ++ tailWord_5701176).sum := by decide
  have hdescent : baseEnd_5701176 < baseStart_5701176 := by decide
  rcases family_descends (prefixWord ++ tailWord_5701176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5701197 : List Nat := [1, 6, 1, 1, 4, 1, 1, 2, 1, 3, 2]
def baseStart_5701197 : Nat := 118140960795 + 5701197 * 2 ^ 59
def prefixEnd_5701197 : Nat := 4983230072969 + 3 ^ 40 * 5701197 * 2
def baseEnd_5701197 : Nat := 2927454366971235774218179

theorem tailTrace_5701197 : CollatzResearch.WordTrace tailWord_5701197 prefixEnd_5701197 2927454366971235774218179 := by
  unfold tailWord_5701197
  simp only [CollatzResearch.WordTrace]
  refine ⟨207939737526544430773533845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138626491684362953849022563 207939737526544430773533845)
  ·
    refine ⟨9747175196556770192509399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 207939737526544430773533845 9747175196556770192509399)
    ·
      refine ⟨14620762794835155288764099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9747175196556770192509399 14620762794835155288764099)
      ·
        refine ⟨21931144192252732933146149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14620762794835155288764099 21931144192252732933146149)
        ·
          refine ⟨4112089536047387424964903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21931144192252732933146149 4112089536047387424964903)
          ·
            refine ⟨6168134304071081137447355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4112089536047387424964903 6168134304071081137447355)
            ·
              refine ⟨9252201456106621706171033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6168134304071081137447355 9252201456106621706171033)
              ·
                refine ⟨6939151092079966279628275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9252201456106621706171033 6939151092079966279628275)
                ·
                  refine ⟨10408726638119949419442413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6939151092079966279628275 10408726638119949419442413)
                  ·
                    refine ⟨3903272489294981032290905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10408726638119949419442413 3903272489294981032290905)
                    ·
                      refine ⟨2927454366971235774218179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3903272489294981032290905 2927454366971235774218179)
                      ·
                        rfl

theorem cell23_5701197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_5701197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5701197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5701197 prefixEnd_5701197 := by exact prefixLift 5701197
  have htrace : WordTrace (prefixWord ++ tailWord_5701197) baseStart_5701197 baseEnd_5701197 := by
    simpa [prefixWord, tailWord_5701197, baseEnd_5701197] using wordTrace_append hprefix tailTrace_5701197
  have hstable : (prefixWord ++ tailWord_5701197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5701197).length < 2 ^ (prefixWord ++ tailWord_5701197).sum := by decide
  have hdescent : baseEnd_5701197 < baseStart_5701197 := by decide
  rcases family_descends (prefixWord ++ tailWord_5701197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5701259 : List Nat := [1, 1, 1, 1, 4, 1, 5, 2, 3, 4]
def baseStart_5701259 : Nat := 118140960795 + 5701259 * 2 ^ 59
def prefixEnd_5701259 : Nat := 4983230072969 + 3 ^ 40 * 5701259 * 2
def baseEnd_5701259 : Nat := 975828734257271510547631

theorem tailTrace_5701259 : CollatzResearch.WordTrace tailWord_5701259 prefixEnd_5701259 975828734257271510547631 := by
  unfold tailWord_5701259
  simp only [CollatzResearch.WordTrace]
  refine ⟨207941998852319815362290831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138627999234879876908193887 207941998852319815362290831)
  ·
    refine ⟨311912998278479723043436247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207941998852319815362290831 311912998278479723043436247)
    ·
      refine ⟨467869497417719584565154371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311912998278479723043436247 467869497417719584565154371)
      ·
        refine ⟨701804246126579376847731557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 467869497417719584565154371 701804246126579376847731557)
        ·
          refine ⟨131588296148733633158949667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 701804246126579376847731557 131588296148733633158949667)
          ·
            refine ⟨197382444223100449738424501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131588296148733633158949667 197382444223100449738424501)
            ·
              refine ⟨18504604145915667162977297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 197382444223100449738424501 18504604145915667162977297)
              ·
                refine ⟨13878453109436750372232973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18504604145915667162977297 13878453109436750372232973)
                ·
                  refine ⟨5204419916038781389587365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13878453109436750372232973 5204419916038781389587365)
                  ·
                    refine ⟨975828734257271510547631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5204419916038781389587365 975828734257271510547631)
                    ·
                      rfl

theorem cell23_5701259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2, 3, 4].length) (baseStart_5701259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5701259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5701259 prefixEnd_5701259 := by exact prefixLift 5701259
  have htrace : WordTrace (prefixWord ++ tailWord_5701259) baseStart_5701259 baseEnd_5701259 := by
    simpa [prefixWord, tailWord_5701259, baseEnd_5701259] using wordTrace_append hprefix tailTrace_5701259
  have hstable : (prefixWord ++ tailWord_5701259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5701259).length < 2 ^ (prefixWord ++ tailWord_5701259).sum := by decide
  have hdescent : baseEnd_5701259 < baseStart_5701259 := by decide
  rcases family_descends (prefixWord ++ tailWord_5701259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5701266 : List Nat := [3, 2, 3, 1, 3, 1, 1, 1, 1, 3, 4]
def baseStart_5701266 : Nat := 118140960795 + 5701266 * 2 ^ 59
def prefixEnd_5701266 : Nat := 4983230072969 + 3 ^ 40 * 5701266 * 2
def baseEnd_5701266 : Nat := 2927489797136396004255361

theorem tailTrace_5701266 : CollatzResearch.WordTrace tailWord_5701266 prefixEnd_5701266 2927489797136396004255361 := by
  unfold tailWord_5701266
  simp only [CollatzResearch.WordTrace]
  refine ⟨51985563540823613889448913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138628169442196303705197101 51985563540823613889448913)
  ·
    refine ⟨38989172655617710417086685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51985563540823613889448913 38989172655617710417086685)
    ·
      refine ⟨14620939745856641406407507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38989172655617710417086685 14620939745856641406407507)
      ·
        refine ⟨21931409618784962109611261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14620939745856641406407507 21931409618784962109611261)
        ·
          refine ⟨8224278607044360791104223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21931409618784962109611261 8224278607044360791104223)
          ·
            refine ⟨12336417910566541186656335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8224278607044360791104223 12336417910566541186656335)
            ·
              refine ⟨18504626865849811779984503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12336417910566541186656335 18504626865849811779984503)
              ·
                refine ⟨27756940298774717669976755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18504626865849811779984503 27756940298774717669976755)
                ·
                  refine ⟨41635410448162076504965133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27756940298774717669976755 41635410448162076504965133)
                  ·
                    refine ⟨15613278918060778689361925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41635410448162076504965133 15613278918060778689361925)
                    ·
                      refine ⟨2927489797136396004255361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15613278918060778689361925 2927489797136396004255361)
                      ·
                        rfl

theorem cell23_5701266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_5701266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5701266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5701266 prefixEnd_5701266 := by exact prefixLift 5701266
  have htrace : WordTrace (prefixWord ++ tailWord_5701266) baseStart_5701266 baseEnd_5701266 := by
    simpa [prefixWord, tailWord_5701266, baseEnd_5701266] using wordTrace_append hprefix tailTrace_5701266
  have hstable : (prefixWord ++ tailWord_5701266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5701266).length < 2 ^ (prefixWord ++ tailWord_5701266).sum := by decide
  have hdescent : baseEnd_5701266 < baseStart_5701266 := by decide
  rcases family_descends (prefixWord ++ tailWord_5701266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5701293 : List Nat := [1, 5, 2, 1, 1, 1, 1, 6, 1, 4]
def baseStart_5701293 : Nat := 118140960795 + 5701293 * 2 ^ 59
def prefixEnd_5701293 : Nat := 4983230072969 + 3 ^ 40 * 5701293 * 2
def baseEnd_5701293 : Nat := 975834553704689132872579

theorem tailTrace_5701293 : CollatzResearch.WordTrace tailWord_5701293 prefixEnd_5701293 975834553704689132872579 := by
  unfold tailWord_5701293
  simp only [CollatzResearch.WordTrace]
  refine ⟨207943238934196639169028533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138628825956131092779352355 207943238934196639169028533)
  ·
    refine ⟨19494678650080934922096425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 207943238934196639169028533 19494678650080934922096425)
    ·
      refine ⟨14621008987560701191572319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19494678650080934922096425 14621008987560701191572319)
      ·
        refine ⟨21931513481341051787358479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14621008987560701191572319 21931513481341051787358479)
        ·
          refine ⟨32897270222011577681037719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21931513481341051787358479 32897270222011577681037719)
          ·
            refine ⟨49345905333017366521556579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32897270222011577681037719 49345905333017366521556579)
            ·
              refine ⟨74018857999526049782334869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49345905333017366521556579 74018857999526049782334869)
              ·
                refine ⟨3469633968727783583546947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 74018857999526049782334869 3469633968727783583546947)
                ·
                  refine ⟨5204450953091675375320421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3469633968727783583546947 5204450953091675375320421)
                  ·
                    refine ⟨975834553704689132872579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5204450953091675375320421 975834553704689132872579)
                    ·
                      rfl

theorem cell23_5701293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_5701293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5701293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5701293 prefixEnd_5701293 := by exact prefixLift 5701293
  have htrace : WordTrace (prefixWord ++ tailWord_5701293) baseStart_5701293 baseEnd_5701293 := by
    simpa [prefixWord, tailWord_5701293, baseEnd_5701293] using wordTrace_append hprefix tailTrace_5701293
  have hstable : (prefixWord ++ tailWord_5701293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5701293).length < 2 ^ (prefixWord ++ tailWord_5701293).sum := by decide
  have hdescent : baseEnd_5701293 < baseStart_5701293 := by decide
  rcases family_descends (prefixWord ++ tailWord_5701293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5701306 : List Nat := [3, 1, 1, 1, 2, 5, 3, 1, 6]
def baseStart_5701306 : Nat := 118140960795 + 5701306 * 2 ^ 59
def prefixEnd_5701306 : Nat := 4983230072969 + 3 ^ 40 * 5701306 * 2
def baseEnd_5701306 : Nat := 325278926262508427528353

theorem tailTrace_5701306 : CollatzResearch.WordTrace tailWord_5701306 prefixEnd_5701306 325278926262508427528353 := by
  unfold tailWord_5701306
  simp only [CollatzResearch.WordTrace]
  refine ⟨51985928270787385597312943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138629142055433028259501181 51985928270787385597312943)
  ·
    refine ⟨77978892406181078395969415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51985928270787385597312943 77978892406181078395969415)
    ·
      refine ⟨116968338609271617593954123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77978892406181078395969415 116968338609271617593954123)
      ·
        refine ⟨175452507913907426390931185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116968338609271617593954123 175452507913907426390931185)
        ·
          refine ⟨131589380935430569793198389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175452507913907426390931185 131589380935430569793198389)
          ·
            refine ⟨12336504462696615918112349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 131589380935430569793198389 12336504462696615918112349)
            ·
              refine ⟨4626189173511230969292131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12336504462696615918112349 4626189173511230969292131)
              ·
                refine ⟨6939283760266846453938197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4626189173511230969292131 6939283760266846453938197)
                ·
                  refine ⟨325278926262508427528353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6939283760266846453938197 325278926262508427528353)
                  ·
                    rfl

theorem cell23_5701306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 1, 6].length) (baseStart_5701306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5701306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5701306 prefixEnd_5701306 := by exact prefixLift 5701306
  have htrace : WordTrace (prefixWord ++ tailWord_5701306) baseStart_5701306 baseEnd_5701306 := by
    simpa [prefixWord, tailWord_5701306, baseEnd_5701306] using wordTrace_append hprefix tailTrace_5701306
  have hstable : (prefixWord ++ tailWord_5701306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5701306).length < 2 ^ (prefixWord ++ tailWord_5701306).sum := by decide
  have hdescent : baseEnd_5701306 < baseStart_5701306 := by decide
  rcases family_descends (prefixWord ++ tailWord_5701306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5701326 : List Nat := [4, 1, 1, 1, 3, 1, 1, 3, 1, 5, 2]
def baseStart_5701326 : Nat := 118140960795 + 5701326 * 2 ^ 59
def prefixEnd_5701326 : Nat := 4983230072969 + 3 ^ 40 * 5701326 * 2
def baseEnd_5701326 : Nat := 2927520605975665769505085

theorem tailTrace_5701326 : CollatzResearch.WordTrace tailWord_5701326 prefixEnd_5701326 2927520605975665769505085 := by
  unfold tailWord_5701326
  simp only [CollatzResearch.WordTrace]
  refine ⟨25993055317884635725622479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138629628362051390536653221 25993055317884635725622479)
  ·
    refine ⟨38989582976826953588433719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25993055317884635725622479 38989582976826953588433719)
    ·
      refine ⟨58484374465240430382650579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38989582976826953588433719 58484374465240430382650579)
      ·
        refine ⟨87726561697860645573975869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58484374465240430382650579 87726561697860645573975869)
        ·
          refine ⟨32897460636697742090240951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87726561697860645573975869 32897460636697742090240951)
          ·
            refine ⟨49346190955046613135361427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32897460636697742090240951 49346190955046613135361427)
            ·
              refine ⟨74019286432569919703042141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49346190955046613135361427 74019286432569919703042141)
              ·
                refine ⟨27757232412213719888640803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74019286432569919703042141 27757232412213719888640803)
                ·
                  refine ⟨41635848618320579832961205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27757232412213719888640803 41635848618320579832961205)
                  ·
                    refine ⟨3903360807967554359340113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41635848618320579832961205 3903360807967554359340113)
                    ·
                      refine ⟨2927520605975665769505085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3903360807967554359340113 2927520605975665769505085)
                      ·
                        rfl

theorem cell23_5701326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 1, 5, 2].length) (baseStart_5701326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5701326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5701326 prefixEnd_5701326 := by exact prefixLift 5701326
  have htrace : WordTrace (prefixWord ++ tailWord_5701326) baseStart_5701326 baseEnd_5701326 := by
    simpa [prefixWord, tailWord_5701326, baseEnd_5701326] using wordTrace_append hprefix tailTrace_5701326
  have hstable : (prefixWord ++ tailWord_5701326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5701326).length < 2 ^ (prefixWord ++ tailWord_5701326).sum := by decide
  have hdescent : baseEnd_5701326 < baseStart_5701326 := by decide
  rcases family_descends (prefixWord ++ tailWord_5701326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5701359 : List Nat := [1, 1, 2, 1, 5, 1, 1, 4, 1, 1, 5]
def baseStart_5701359 : Nat := 118140960795 + 5701359 * 2 ^ 59
def prefixEnd_5701359 : Nat := 4983230072969 + 3 ^ 40 * 5701359 * 2
def baseEnd_5701359 : Nat := 2927537550837264140392433

theorem tailTrace_5701359 : CollatzResearch.WordTrace tailWord_5701359 prefixEnd_5701359 2927537550837264140392433 := by
  unfold tailWord_5701359
  simp only [CollatzResearch.WordTrace]
  refine ⟨207945646151957532440931131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138630430767971688293954087 207945646151957532440931131)
  ·
    refine ⟨311918469227936298661396697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207945646151957532440931131 311918469227936298661396697)
    ·
      refine ⟨233938851920952223996047523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311918469227936298661396697 233938851920952223996047523)
      ·
        refine ⟨350908277881428335994071285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233938851920952223996047523 350908277881428335994071285)
        ·
          refine ⟨32897651051383906499444183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 350908277881428335994071285 32897651051383906499444183)
          ·
            refine ⟨49346476577075859749166275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32897651051383906499444183 49346476577075859749166275)
            ·
              refine ⟨74019714865613789623749413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49346476577075859749166275 74019714865613789623749413)
              ·
                refine ⟨13878696537302585554453015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74019714865613789623749413 13878696537302585554453015)
                ·
                  refine ⟨20818044805953878331679523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13878696537302585554453015 20818044805953878331679523)
                  ·
                    refine ⟨31227067208930817497519285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20818044805953878331679523 31227067208930817497519285)
                    ·
                      refine ⟨2927537550837264140392433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31227067208930817497519285 2927537550837264140392433)
                      ·
                        rfl

theorem cell23_5701359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4, 1, 1, 5].length) (baseStart_5701359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5701359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5701359 prefixEnd_5701359 := by exact prefixLift 5701359
  have htrace : WordTrace (prefixWord ++ tailWord_5701359) baseStart_5701359 baseEnd_5701359 := by
    simpa [prefixWord, tailWord_5701359, baseEnd_5701359] using wordTrace_append hprefix tailTrace_5701359
  have hstable : (prefixWord ++ tailWord_5701359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5701359).length < 2 ^ (prefixWord ++ tailWord_5701359).sum := by decide
  have hdescent : baseEnd_5701359 < baseStart_5701359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5701359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5701386 : List Nat := [3, 1, 2, 2, 1, 4, 1, 2, 1, 2, 4]
def baseStart_5701386 : Nat := 118140960795 + 5701386 * 2 ^ 59
def prefixEnd_5701386 : Nat := 4983230072969 + 3 ^ 40 * 5701386 * 2
def baseEnd_5701386 : Nat := 2927551414814935534754809

theorem tailTrace_5701386 : CollatzResearch.WordTrace tailWord_5701386 prefixEnd_5701386 2927551414814935534754809 := by
  unfold tailWord_5701386
  simp only [CollatzResearch.WordTrace]
  refine ⟨51986657730714929013041003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138631087281906477368109341 51986657730714929013041003)
  ·
    refine ⟨77979986596072393519561505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51986657730714929013041003 77979986596072393519561505)
    ·
      refine ⟨58484989947054295139671129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77979986596072393519561505 58484989947054295139671129)
      ·
        refine ⟨43863742460290721354753347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58484989947054295139671129 43863742460290721354753347)
        ·
          refine ⟨65795613690436082032130021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43863742460290721354753347 65795613690436082032130021)
          ·
            refine ⟨12336677566956765381024379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65795613690436082032130021 12336677566956765381024379)
            ·
              refine ⟨18505016350435148071536569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12336677566956765381024379 18505016350435148071536569)
              ·
                refine ⟨13878762262826361053652427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18505016350435148071536569 13878762262826361053652427)
                ·
                  refine ⟨20818143394239541580478641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13878762262826361053652427 20818143394239541580478641)
                  ·
                    refine ⟨15613607545679656185358981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20818143394239541580478641 15613607545679656185358981)
                    ·
                      refine ⟨2927551414814935534754809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15613607545679656185358981 2927551414814935534754809)
                      ·
                        rfl

theorem cell23_5701386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_5701386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5701386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5701386 prefixEnd_5701386 := by exact prefixLift 5701386
  have htrace : WordTrace (prefixWord ++ tailWord_5701386) baseStart_5701386 baseEnd_5701386 := by
    simpa [prefixWord, tailWord_5701386, baseEnd_5701386] using wordTrace_append hprefix tailTrace_5701386
  have hstable : (prefixWord ++ tailWord_5701386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5701386).length < 2 ^ (prefixWord ++ tailWord_5701386).sum := by decide
  have hdescent : baseEnd_5701386 < baseStart_5701386 := by decide
  rcases family_descends (prefixWord ++ tailWord_5701386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5701409 : List Nat := [1, 2, 3, 2, 1, 3, 1, 1, 2, 7]
def baseStart_5701409 : Nat := 118140960795 + 5701409 * 2 ^ 59
def prefixEnd_5701409 : Nat := 4983230072969 + 3 ^ 40 * 5701409 * 2
def baseEnd_5701409 : Nat := 975854408289996314922401

theorem tailTrace_5701409 : CollatzResearch.WordTrace tailWord_5701409 prefixEnd_5701409 975854408289996314922401 := by
  unfold tailWord_5701409
  simp only [CollatzResearch.WordTrace]
  refine ⟨207947469801776390980251281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138631646534517593986834187 207947469801776390980251281)
  ·
    refine ⟨155960602351332293235188461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207947469801776390980251281 155960602351332293235188461)
    ·
      refine ⟨58485225881749609963195673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155960602351332293235188461 58485225881749609963195673)
      ·
        refine ⟨43863919411312207472396755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58485225881749609963195673 43863919411312207472396755)
        ·
          refine ⟨65795879116968311208595133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43863919411312207472396755 65795879116968311208595133)
          ·
            refine ⟨24673454668863116703223175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65795879116968311208595133 24673454668863116703223175)
            ·
              refine ⟨37010182003294675054834763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24673454668863116703223175 37010182003294675054834763)
              ·
                refine ⟨55515273004942012582252145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37010182003294675054834763 55515273004942012582252145)
                ·
                  refine ⟨41636454753706509436689109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55515273004942012582252145 41636454753706509436689109)
                  ·
                    refine ⟨975854408289996314922401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41636454753706509436689109 975854408289996314922401)
                    ·
                      rfl

theorem cell23_5701409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 7].length) (baseStart_5701409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5701409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5701409 prefixEnd_5701409 := by exact prefixLift 5701409
  have htrace : WordTrace (prefixWord ++ tailWord_5701409) baseStart_5701409 baseEnd_5701409 := by
    simpa [prefixWord, tailWord_5701409, baseEnd_5701409] using wordTrace_append hprefix tailTrace_5701409
  have hstable : (prefixWord ++ tailWord_5701409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5701409).length < 2 ^ (prefixWord ++ tailWord_5701409).sum := by decide
  have hdescent : baseEnd_5701409 < baseStart_5701409 := by decide
  rcases family_descends (prefixWord ++ tailWord_5701409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
