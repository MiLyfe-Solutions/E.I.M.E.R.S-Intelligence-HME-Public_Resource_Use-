import V185TrunkScan19Chunk001

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace V185TrunkScan19Incremental

def tailWord_19457 : List Nat := [1, 2, 4, 1, 2, 4, 1, 4]
def baseStart_19457 : Nat := 118140960795 + 19457 * 2 ^ 59
def prefixEnd_19457 : Nat := 4983230072969 + 3 ^ 40 * 19457 * 2
def baseEnd_19457 : Nat := 5920469982006286280311

theorem tailTrace_19457 : CollatzResearch.WordTrace tailWord_19457 prefixEnd_19457 5920469982006286280311 := by
  unfold tailWord_19457
  simp only [CollatzResearch.WordTrace]
  refine ⟨709655090518086836152625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 473103393678724557435083 709655090518086836152625)
  ·
    refine ⟨532241317888565127114469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 709655090518086836152625 532241317888565127114469)
    ·
      refine ⟨99795247104105961333963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 532241317888565127114469 99795247104105961333963)
      ·
        refine ⟨149692870656158942000945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99795247104105961333963 149692870656158942000945)
        ·
          refine ⟨112269652992119206500709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149692870656158942000945 112269652992119206500709)
          ·
            refine ⟨21050559936022351218883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112269652992119206500709 21050559936022351218883)
            ·
              refine ⟨31575839904033526828325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21050559936022351218883 31575839904033526828325)
              ·
                refine ⟨5920469982006286280311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31575839904033526828325 5920469982006286280311)
                ·
                  rfl

theorem cell19_19457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 4].length) (baseStart_19457 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_19457 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_19457 prefixEnd_19457 := by exact prefixLift 19457
  have htrace : WordTrace (prefixWord ++ tailWord_19457) baseStart_19457 baseEnd_19457 := by
    simpa [prefixWord, tailWord_19457, baseEnd_19457] using wordTrace_append hprefix tailTrace_19457
  have hstable : (prefixWord ++ tailWord_19457).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19457).length < 2 ^ (prefixWord ++ tailWord_19457).sum := by decide
  have hdescent : baseEnd_19457 < baseStart_19457 := by decide
  rcases family_descends (prefixWord ++ tailWord_19457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19495 : List Nat := [1, 1, 7, 1, 1, 2, 6]
def baseStart_19495 : Nat := 118140960795 + 19495 * 2 ^ 59
def prefixEnd_19495 : Nat := 4983230072969 + 3 ^ 40 * 19495 * 2
def baseEnd_19495 : Nat := 1977344268544485811921

theorem tailTrace_19495 : CollatzResearch.WordTrace tailWord_19495 prefixEnd_19495 1977344268544485811921 := by
  unfold tailWord_19495
  simp only [CollatzResearch.WordTrace]
  refine ⟨711041064380419326035939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 474027376253612884023959 711041064380419326035939)
  ·
    refine ⟨1066561596570628989053909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 711041064380419326035939 1066561596570628989053909)
    ·
      refine ⟨24997537419624116930951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 1066561596570628989053909 24997537419624116930951)
      ·
        refine ⟨37496306129436175396427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24997537419624116930951 37496306129436175396427)
        ·
          refine ⟨56244459194154263094641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37496306129436175396427 56244459194154263094641)
          ·
            refine ⟨42183344395615697320981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56244459194154263094641 42183344395615697320981)
            ·
              refine ⟨1977344268544485811921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 42183344395615697320981 1977344268544485811921)
              ·
                rfl

theorem cell19_19495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 6].length) (baseStart_19495 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_19495 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_19495 prefixEnd_19495 := by exact prefixLift 19495
  have htrace : WordTrace (prefixWord ++ tailWord_19495) baseStart_19495 baseEnd_19495 := by
    simpa [prefixWord, tailWord_19495, baseEnd_19495] using wordTrace_append hprefix tailTrace_19495
  have hstable : (prefixWord ++ tailWord_19495).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19495).length < 2 ^ (prefixWord ++ tailWord_19495).sum := by decide
  have hdescent : baseEnd_19495 < baseStart_19495 := by decide
  rcases family_descends (prefixWord ++ tailWord_19495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19499 : List Nat := [1, 1, 1, 1, 2, 1, 12]
def baseStart_19499 : Nat := 118140960795 + 19499 * 2 ^ 59
def prefixEnd_19499 : Nat := 4983230072969 + 3 ^ 40 * 19499 * 2
def baseEnd_19499 : Nat := 1977749981654211115621

theorem tailTrace_19499 : CollatzResearch.WordTrace tailWord_19499 prefixEnd_19499 1977749981654211115621 := by
  unfold tailWord_19499
  simp only [CollatzResearch.WordTrace]
  refine ⟨711186956365928009181551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 474124637577285339454367 711186956365928009181551)
  ·
    refine ⟨1066780434548892013772327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 711186956365928009181551 1066780434548892013772327)
    ·
      refine ⟨1600170651823338020658491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1066780434548892013772327 1600170651823338020658491)
      ·
        refine ⟨2400255977735007030987737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1600170651823338020658491 2400255977735007030987737)
        ·
          refine ⟨1800191983301255273240803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2400255977735007030987737 1800191983301255273240803)
          ·
            refine ⟨2700287974951882909861205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1800191983301255273240803 2700287974951882909861205)
            ·
              refine ⟨1977749981654211115621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 2700287974951882909861205 1977749981654211115621)
              ·
                rfl

theorem cell19_19499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 12].length) (baseStart_19499 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_19499 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_19499 prefixEnd_19499 := by exact prefixLift 19499
  have htrace : WordTrace (prefixWord ++ tailWord_19499) baseStart_19499 baseEnd_19499 := by
    simpa [prefixWord, tailWord_19499, baseEnd_19499] using wordTrace_append hprefix tailTrace_19499
  have hstable : (prefixWord ++ tailWord_19499).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19499).length < 2 ^ (prefixWord ++ tailWord_19499).sum := by decide
  have hdescent : baseEnd_19499 < baseStart_19499 := by decide
  rcases family_descends (prefixWord ++ tailWord_19499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19533 : List Nat := [1, 6, 1, 1, 1, 3, 1, 5]
def baseStart_19533 : Nat := 118140960795 + 19533 * 2 ^ 59
def prefixEnd_19533 : Nat := 4983230072969 + 3 ^ 40 * 19533 * 2
def baseEnd_19533 : Nat := 5943595629260628591215

theorem tailTrace_19533 : CollatzResearch.WordTrace tailWord_19533 prefixEnd_19533 5943595629260628591215 := by
  unfold tailWord_19533
  simp only [CollatzResearch.WordTrace]
  refine ⟨712427038242751815919253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 474951358828501210612835 712427038242751815919253)
  ·
    refine ⟨33395017417628991371215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 712427038242751815919253 33395017417628991371215)
    ·
      refine ⟨50092526126443487056823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33395017417628991371215 50092526126443487056823)
      ·
        refine ⟨75138789189665230585235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50092526126443487056823 75138789189665230585235)
        ·
          refine ⟨112708183784497845877853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75138789189665230585235 112708183784497845877853)
          ·
            refine ⟨42265568919186692204195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112708183784497845877853 42265568919186692204195)
            ·
              refine ⟨63398353378780038306293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42265568919186692204195 63398353378780038306293)
              ·
                refine ⟨5943595629260628591215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63398353378780038306293 5943595629260628591215)
                ·
                  rfl

theorem cell19_19533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 5].length) (baseStart_19533 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_19533 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_19533 prefixEnd_19533 := by exact prefixLift 19533
  have htrace : WordTrace (prefixWord ++ tailWord_19533) baseStart_19533 baseEnd_19533 := by
    simpa [prefixWord, tailWord_19533, baseEnd_19533] using wordTrace_append hprefix tailTrace_19533
  have hstable : (prefixWord ++ tailWord_19533).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19533).length < 2 ^ (prefixWord ++ tailWord_19533).sum := by decide
  have hdescent : baseEnd_19533 < baseStart_19533 := by decide
  rcases family_descends (prefixWord ++ tailWord_19533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19550 : List Nat := [4, 4, 1, 1, 1, 1, 7]
def baseStart_19550 : Nat := 118140960795 + 19550 * 2 ^ 59
def prefixEnd_19550 : Nat := 4983230072969 + 3 ^ 40 * 19550 * 2
def baseEnd_19550 : Nat := 1982922823803208737797

theorem tailTrace_19550 : CollatzResearch.WordTrace tailWord_19550 prefixEnd_19550 1982922823803208737797 := by
  unfold tailWord_19550
  simp only [CollatzResearch.WordTrace]
  refine ⟨89130884897645464911013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 475364719454109146192069 89130884897645464911013)
  ·
    refine ⟨16712040918308524670815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89130884897645464911013 16712040918308524670815)
    ·
      refine ⟨25068061377462787006223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16712040918308524670815 25068061377462787006223)
      ·
        refine ⟨37602092066194180509335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25068061377462787006223 37602092066194180509335)
        ·
          refine ⟨56403138099291270764003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37602092066194180509335 56403138099291270764003)
          ·
            refine ⟨84604707148936906146005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56403138099291270764003 84604707148936906146005)
            ·
              refine ⟨1982922823803208737797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 84604707148936906146005 1982922823803208737797)
              ·
                rfl

theorem cell19_19550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 7].length) (baseStart_19550 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_19550 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_19550 prefixEnd_19550 := by exact prefixLift 19550
  have htrace : WordTrace (prefixWord ++ tailWord_19550) baseStart_19550 baseEnd_19550 := by
    simpa [prefixWord, tailWord_19550, baseEnd_19550] using wordTrace_append hprefix tailTrace_19550
  have hstable : (prefixWord ++ tailWord_19550).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19550).length < 2 ^ (prefixWord ++ tailWord_19550).sum := by decide
  have hdescent : baseEnd_19550 < baseStart_19550 := by decide
  rcases family_descends (prefixWord ++ tailWord_19550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19626 : List Nat := [3, 1, 5, 1, 1, 3, 1, 4]
def baseStart_19626 : Nat := 118140960795 + 19626 * 2 ^ 59
def prefixEnd_19626 : Nat := 4983230072969 + 3 ^ 40 * 19626 * 2
def baseEnd_19626 : Nat := 5971894118663968524295

theorem tailTrace_19626 : CollatzResearch.WordTrace tailWord_19626 prefixEnd_19626 5971894118663968524295 := by
  unfold tailWord_19626
  simp only [CollatzResearch.WordTrace]
  refine ⟨178954756726457174763683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 477212684603885799369821 178954756726457174763683)
  ·
    refine ⟨268432135089685762145525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178954756726457174763683 268432135089685762145525)
    ·
      refine ⟨25165512664658040201143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 268432135089685762145525 25165512664658040201143)
      ·
        refine ⟨37748268996987060301715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25165512664658040201143 37748268996987060301715)
        ·
          refine ⟨56622403495480590452573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37748268996987060301715 56622403495480590452573)
          ·
            refine ⟨21233401310805221419715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56622403495480590452573 21233401310805221419715)
            ·
              refine ⟨31850101966207832129573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21233401310805221419715 31850101966207832129573)
              ·
                refine ⟨5971894118663968524295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31850101966207832129573 5971894118663968524295)
                ·
                  rfl

theorem cell19_19626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 4].length) (baseStart_19626 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_19626 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_19626 prefixEnd_19626 := by exact prefixLift 19626
  have htrace : WordTrace (prefixWord ++ tailWord_19626) baseStart_19626 baseEnd_19626 := by
    simpa [prefixWord, tailWord_19626, baseEnd_19626] using wordTrace_append hprefix tailTrace_19626
  have hstable : (prefixWord ++ tailWord_19626).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19626).length < 2 ^ (prefixWord ++ tailWord_19626).sum := by decide
  have hdescent : baseEnd_19626 < baseStart_19626 := by decide
  rcases family_descends (prefixWord ++ tailWord_19626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19700 : List Nat := [2, 6, 1, 2, 1, 1, 1, 5]
def baseStart_19700 : Nat := 118140960795 + 19700 * 2 ^ 59
def prefixEnd_19700 : Nat := 4983230072969 + 3 ^ 40 * 19700 * 2
def baseEnd_19700 : Nat := 5994411196253722879649

theorem tailTrace_19700 : CollatzResearch.WordTrace tailWord_19700 prefixEnd_19700 5994411196253722879649 := by
  unfold tailWord_19700
  simp only [CollatzResearch.WordTrace]
  refine ⟨359259014318869668624277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 479012019091826224832369 359259014318869668624277)
  ·
    refine ⟨16840266296197015716763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 359259014318869668624277 16840266296197015716763)
    ·
      refine ⟨25260399444295523575145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16840266296197015716763 25260399444295523575145)
      ·
        refine ⟨18945299583221642681359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25260399444295523575145 18945299583221642681359)
        ·
          refine ⟨28417949374832464022039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18945299583221642681359 28417949374832464022039)
          ·
            refine ⟨42626924062248696033059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28417949374832464022039 42626924062248696033059)
            ·
              refine ⟨63940386093373044049589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42626924062248696033059 63940386093373044049589)
              ·
                refine ⟨5994411196253722879649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63940386093373044049589 5994411196253722879649)
                ·
                  rfl

theorem cell19_19700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 5].length) (baseStart_19700 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_19700 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_19700 prefixEnd_19700 := by exact prefixLift 19700
  have htrace : WordTrace (prefixWord ++ tailWord_19700) baseStart_19700 baseEnd_19700 := by
    simpa [prefixWord, tailWord_19700, baseEnd_19700] using wordTrace_append hprefix tailTrace_19700
  have hstable : (prefixWord ++ tailWord_19700).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19700).length < 2 ^ (prefixWord ++ tailWord_19700).sum := by decide
  have hdescent : baseEnd_19700 < baseStart_19700 := by decide
  rcases family_descends (prefixWord ++ tailWord_19700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19966 : List Nat := [4, 2, 2, 3, 2, 1, 1, 4]
def baseStart_19966 : Nat := 118140960795 + 19966 * 2 ^ 59
def prefixEnd_19966 : Nat := 4983230072969 + 3 ^ 40 * 19966 * 2
def baseEnd_19966 : Nat := 6075350961643920967813

theorem tailTrace_19966 : CollatzResearch.WordTrace tailWord_19966 prefixEnd_19966 6075350961643920967813 := by
  unfold tailWord_19966
  simp only [CollatzResearch.WordTrace]
  refine ⟨91027480709258345803969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 485479897116044510954501 91027480709258345803969)
  ·
    refine ⟨68270610531943759352977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91027480709258345803969 68270610531943759352977)
    ·
      refine ⟨51202957898957819514733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68270610531943759352977 51202957898957819514733)
      ·
        refine ⟨19201109212109182318025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51202957898957819514733 19201109212109182318025)
        ·
          refine ⟨14400831909081886738519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19201109212109182318025 14400831909081886738519)
          ·
            refine ⟨21601247863622830107779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14400831909081886738519 21601247863622830107779)
            ·
              refine ⟨32401871795434245161669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21601247863622830107779 32401871795434245161669)
              ·
                refine ⟨6075350961643920967813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32401871795434245161669 6075350961643920967813)
                ·
                  rfl

theorem cell19_19966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_19966 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_19966 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_19966 prefixEnd_19966 := by exact prefixLift 19966
  have htrace : WordTrace (prefixWord ++ tailWord_19966) baseStart_19966 baseEnd_19966 := by
    simpa [prefixWord, tailWord_19966, baseEnd_19966] using wordTrace_append hprefix tailTrace_19966
  have hstable : (prefixWord ++ tailWord_19966).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19966).length < 2 ^ (prefixWord ++ tailWord_19966).sum := by decide
  have hdescent : baseEnd_19966 < baseStart_19966 := by decide
  rcases family_descends (prefixWord ++ tailWord_19966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19970 : List Nat := [3, 4, 1, 2, 1, 1, 3, 4]
def baseStart_19970 : Nat := 118140960795 + 19970 * 2 ^ 59
def prefixEnd_19970 : Nat := 4983230072969 + 3 ^ 40 * 19970 * 2
def baseEnd_19970 : Nat := 6076568100973096878913

theorem tailTrace_19970 : CollatzResearch.WordTrace tailWord_19970 prefixEnd_19970 6076568100973096878913 := by
  unfold tailWord_19970
  simp only [CollatzResearch.WordTrace]
  refine ⟨182091434414893862394341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 485577158439716966384909 182091434414893862394341)
  ·
    refine ⟨34142143952792599198939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 182091434414893862394341 34142143952792599198939)
    ·
      refine ⟨51213215929188898798409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34142143952792599198939 51213215929188898798409)
      ·
        refine ⟨38409911946891674098807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51213215929188898798409 38409911946891674098807)
        ·
          refine ⟨57614867920337511148211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38409911946891674098807 57614867920337511148211)
          ·
            refine ⟨86422301880506266722317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57614867920337511148211 86422301880506266722317)
            ·
              refine ⟨32408363205189850020869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86422301880506266722317 32408363205189850020869)
              ·
                refine ⟨6076568100973096878913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32408363205189850020869 6076568100973096878913)
                ·
                  rfl

theorem cell19_19970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_19970 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_19970 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_19970 prefixEnd_19970 := by exact prefixLift 19970
  have htrace : WordTrace (prefixWord ++ tailWord_19970) baseStart_19970 baseEnd_19970 := by
    simpa [prefixWord, tailWord_19970, baseEnd_19970] using wordTrace_append hprefix tailTrace_19970
  have hstable : (prefixWord ++ tailWord_19970).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19970).length < 2 ^ (prefixWord ++ tailWord_19970).sum := by decide
  have hdescent : baseEnd_19970 < baseStart_19970 := by decide
  rcases family_descends (prefixWord ++ tailWord_19970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20069 : List Nat := [1, 3, 1, 3, 3, 1, 7]
def baseStart_20069 : Nat := 118140960795 + 20069 * 2 ^ 59
def prefixEnd_20069 : Nat := 4983230072969 + 3 ^ 40 * 20069 * 2
def baseEnd_20069 : Nat := 2035564099790066892881

theorem tailTrace_20069 : CollatzResearch.WordTrace tailWord_20069 prefixEnd_20069 2035564099790066892881 := by
  unfold tailWord_20069
  simp only [CollatzResearch.WordTrace]
  refine ⟨731976564300915357431261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 487984376200610238287507 731976564300915357431261)
  ·
    refine ⟨274491211612843259036723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 731976564300915357431261 274491211612843259036723)
    ·
      refine ⟨411736817419264888555085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274491211612843259036723 411736817419264888555085)
      ·
        refine ⟨154401306532224333208157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 411736817419264888555085 154401306532224333208157)
        ·
          refine ⟨57900489949584124953059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154401306532224333208157 57900489949584124953059)
          ·
            refine ⟨86850734924376187429589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57900489949584124953059 86850734924376187429589)
            ·
              refine ⟨2035564099790066892881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 86850734924376187429589 2035564099790066892881)
              ·
                rfl

theorem cell19_20069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 7].length) (baseStart_20069 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_20069 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_20069 prefixEnd_20069 := by exact prefixLift 20069
  have htrace : WordTrace (prefixWord ++ tailWord_20069) baseStart_20069 baseEnd_20069 := by
    simpa [prefixWord, tailWord_20069, baseEnd_20069] using wordTrace_append hprefix tailTrace_20069
  have hstable : (prefixWord ++ tailWord_20069).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20069).length < 2 ^ (prefixWord ++ tailWord_20069).sum := by decide
  have hdescent : baseEnd_20069 < baseStart_20069 := by decide
  rcases family_descends (prefixWord ++ tailWord_20069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20086 : List Nat := [5, 1, 1, 2, 2, 1, 1, 6]
def baseStart_20086 : Nat := 118140960795 + 20086 * 2 ^ 59
def prefixEnd_20086 : Nat := 4983230072969 + 3 ^ 40 * 20086 * 2
def baseEnd_20086 : Nat := 6111865141519198300819

theorem tailTrace_20086 : CollatzResearch.WordTrace tailWord_20086 prefixEnd_20086 6111865141519198300819 := by
  unfold tailWord_20086
  simp only [CollatzResearch.WordTrace]
  refine ⟨45787287827457953800007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 488397736826218173866741 45787287827457953800007)
  ·
    refine ⟨68680931741186930700011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45787287827457953800007 68680931741186930700011)
    ·
      refine ⟨103021397611780396050017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68680931741186930700011 103021397611780396050017)
      ·
        refine ⟨77266048208835297037513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103021397611780396050017 77266048208835297037513)
        ·
          refine ⟨57949536156626472778135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77266048208835297037513 57949536156626472778135)
          ·
            refine ⟨86924304234939709167203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57949536156626472778135 86924304234939709167203)
            ·
              refine ⟨130386456352409563750805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86924304234939709167203 130386456352409563750805)
              ·
                refine ⟨6111865141519198300819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 130386456352409563750805 6111865141519198300819)
                ·
                  rfl

theorem cell19_20086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_20086 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_20086 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_20086 prefixEnd_20086 := by exact prefixLift 20086
  have htrace : WordTrace (prefixWord ++ tailWord_20086) baseStart_20086 baseEnd_20086 := by
    simpa [prefixWord, tailWord_20086, baseEnd_20086] using wordTrace_append hprefix tailTrace_20086
  have hstable : (prefixWord ++ tailWord_20086).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20086).length < 2 ^ (prefixWord ++ tailWord_20086).sum := by decide
  have hdescent : baseEnd_20086 < baseStart_20086 := by decide
  rcases family_descends (prefixWord ++ tailWord_20086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20124 : List Nat := [2, 2, 3, 2, 4, 6]
def baseStart_20124 : Nat := 118140960795 + 20124 * 2 ^ 59
def prefixEnd_20124 : Nat := 4983230072969 + 3 ^ 40 * 20124 * 2
def baseEnd_20124 : Nat := 680380885016263272919

theorem tailTrace_20124 : CollatzResearch.WordTrace tailWord_20124 prefixEnd_20124 680380885016263272919 := by
  unfold tailWord_20124
  simp only [CollatzResearch.WordTrace]
  refine ⟨366991289550829875341713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 489321719401106500455617 366991289550829875341713)
  ·
    refine ⟨275243467163122406506285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 366991289550829875341713 275243467163122406506285)
    ·
      refine ⟨103216300186170902439857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 275243467163122406506285 103216300186170902439857)
      ·
        refine ⟨77412225139628176829893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103216300186170902439857 77412225139628176829893)
        ·
          refine ⟨14514792213680283155605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77412225139628176829893 14514792213680283155605)
          ·
            refine ⟨680380885016263272919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 14514792213680283155605 680380885016263272919)
            ·
              rfl

theorem cell19_20124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 6].length) (baseStart_20124 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_20124 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_20124 prefixEnd_20124 := by exact prefixLift 20124
  have htrace : WordTrace (prefixWord ++ tailWord_20124) baseStart_20124 baseEnd_20124 := by
    simpa [prefixWord, tailWord_20124, baseEnd_20124] using wordTrace_append hprefix tailTrace_20124
  have hstable : (prefixWord ++ tailWord_20124).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20124).length < 2 ^ (prefixWord ++ tailWord_20124).sum := by decide
  have hdescent : baseEnd_20124 < baseStart_20124 := by decide
  rcases family_descends (prefixWord ++ tailWord_20124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20230 : List Nat := [6, 2, 2, 1, 1, 2, 5]
def baseStart_20230 : Nat := 118140960795 + 20230 * 2 ^ 59
def prefixEnd_20230 : Nat := 4983230072969 + 3 ^ 40 * 20230 * 2
def baseEnd_20230 : Nat := 2051894052456510366809

theorem tailTrace_20230 : CollatzResearch.WordTrace tailWord_20230 prefixEnd_20230 2051894052456510366809 := by
  unfold tailWord_20230
  simp only [CollatzResearch.WordTrace]
  refine ⟨23057772397426245438817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 491899144478426569361429 23057772397426245438817)
  ·
    refine ⟨17293329298069684079113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23057772397426245438817 17293329298069684079113)
    ·
      refine ⟨12969996973552263059335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17293329298069684079113 12969996973552263059335)
      ·
        refine ⟨19454995460328394589003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12969996973552263059335 19454995460328394589003)
        ·
          refine ⟨29182493190492591883505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19454995460328394589003 29182493190492591883505)
          ·
            refine ⟨21886869892869443912629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29182493190492591883505 21886869892869443912629)
            ·
              refine ⟨2051894052456510366809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21886869892869443912629 2051894052456510366809)
              ·
                rfl

theorem cell19_20230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 5].length) (baseStart_20230 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_20230 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_20230 prefixEnd_20230 := by exact prefixLift 20230
  have htrace : WordTrace (prefixWord ++ tailWord_20230) baseStart_20230 baseEnd_20230 := by
    simpa [prefixWord, tailWord_20230, baseEnd_20230] using wordTrace_append hprefix tailTrace_20230
  have hstable : (prefixWord ++ tailWord_20230).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20230).length < 2 ^ (prefixWord ++ tailWord_20230).sum := by decide
  have hdescent : baseEnd_20230 < baseStart_20230 := by decide
  rcases family_descends (prefixWord ++ tailWord_20230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20276 : List Nat := [2, 5, 1, 1, 2, 1, 2, 5]
def baseStart_20276 : Nat := 118140960795 + 20276 * 2 ^ 59
def prefixEnd_20276 : Nat := 4983230072969 + 3 ^ 40 * 20276 * 2
def baseEnd_20276 : Nat := 6169679259655054078079

theorem tailTrace_20276 : CollatzResearch.WordTrace tailWord_20276 prefixEnd_20276 6169679259655054078079 := by
  unfold tailWord_20276
  simp only [CollatzResearch.WordTrace]
  refine ⟨369763237275494855108341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 493017649700659806811121 369763237275494855108341)
  ·
    refine ⟨34665303494577642666407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 369763237275494855108341 34665303494577642666407)
    ·
      refine ⟨51997955241866463999611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34665303494577642666407 51997955241866463999611)
      ·
        refine ⟨77996932862799695999417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51997955241866463999611 77996932862799695999417)
        ·
          refine ⟨58497699647099771999563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77996932862799695999417 58497699647099771999563)
          ·
            refine ⟨87746549470649657999345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58497699647099771999563 87746549470649657999345)
            ·
              refine ⟨65809912102987243499509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87746549470649657999345 65809912102987243499509)
              ·
                refine ⟨6169679259655054078079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65809912102987243499509 6169679259655054078079)
                ·
                  rfl

theorem cell19_20276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 5].length) (baseStart_20276 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_20276 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_20276 prefixEnd_20276 := by exact prefixLift 20276
  have htrace : WordTrace (prefixWord ++ tailWord_20276) baseStart_20276 baseEnd_20276 := by
    simpa [prefixWord, tailWord_20276, baseEnd_20276] using wordTrace_append hprefix tailTrace_20276
  have hstable : (prefixWord ++ tailWord_20276).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20276).length < 2 ^ (prefixWord ++ tailWord_20276).sum := by decide
  have hdescent : baseEnd_20276 < baseStart_20276 := by decide
  rcases family_descends (prefixWord ++ tailWord_20276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20386 : List Nat := [3, 3, 1, 2, 4, 1, 2, 3]
def baseStart_20386 : Nat := 118140960795 + 20386 * 2 ^ 59
def prefixEnd_20386 : Nat := 4983230072969 + 3 ^ 40 * 20386 * 2
def baseEnd_20386 : Nat := 6203150591207391633335

theorem tailTrace_20386 : CollatzResearch.WordTrace tailWord_20386 prefixEnd_20386 6203150591207391633335 := by
  unfold tailWord_20386
  simp only [CollatzResearch.WordTrace]
  refine ⟨185884626038119624180253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 495692336101652331147341 185884626038119624180253)
  ·
    refine ⟨69706734764294859067595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185884626038119624180253 69706734764294859067595)
    ·
      refine ⟨104560102146442288601393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69706734764294859067595 104560102146442288601393)
      ·
        refine ⟨78420076609831716451045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104560102146442288601393 78420076609831716451045)
        ·
          refine ⟨14703764364343446834571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78420076609831716451045 14703764364343446834571)
          ·
            refine ⟨22055646546515170251857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14703764364343446834571 22055646546515170251857)
            ·
              refine ⟨16541734909886377688893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22055646546515170251857 16541734909886377688893)
              ·
                refine ⟨6203150591207391633335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16541734909886377688893 6203150591207391633335)
                ·
                  rfl

theorem cell19_20386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 3].length) (baseStart_20386 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_20386 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_20386 prefixEnd_20386 := by exact prefixLift 20386
  have htrace : WordTrace (prefixWord ++ tailWord_20386) baseStart_20386 baseEnd_20386 := by
    simpa [prefixWord, tailWord_20386, baseEnd_20386] using wordTrace_append hprefix tailTrace_20386
  have hstable : (prefixWord ++ tailWord_20386).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20386).length < 2 ^ (prefixWord ++ tailWord_20386).sum := by decide
  have hdescent : baseEnd_20386 < baseStart_20386 := by decide
  rcases family_descends (prefixWord ++ tailWord_20386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20430 : List Nat := [4, 1, 1, 1, 2, 2, 4, 4]
def baseStart_20430 : Nat := 118140960795 + 20430 * 2 ^ 59
def prefixEnd_20430 : Nat := 4983230072969 + 3 ^ 40 * 20430 * 2
def baseEnd_20430 : Nat := 6216539123828326655437

theorem tailTrace_20430 : CollatzResearch.WordTrace tailWord_20430 prefixEnd_20430 6216539123828326655437 := by
  unfold tailWord_20430
  simp only [CollatzResearch.WordTrace]
  refine ⟨93142914499134251415343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 496762210662049340881829 93142914499134251415343)
  ·
    refine ⟨139714371748701377123015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93142914499134251415343 139714371748701377123015)
    ·
      refine ⟨209571557623052065684523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139714371748701377123015 209571557623052065684523)
      ·
        refine ⟨314357336434578098526785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209571557623052065684523 314357336434578098526785)
        ·
          refine ⟨235768002325933573895089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 314357336434578098526785 235768002325933573895089)
          ·
            refine ⟨176826001744450180421317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 235768002325933573895089 176826001744450180421317)
            ·
              refine ⟨33154875327084408828997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 176826001744450180421317 33154875327084408828997)
              ·
                refine ⟨6216539123828326655437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33154875327084408828997 6216539123828326655437)
                ·
                  rfl

theorem cell19_20430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_20430 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_20430 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_20430 prefixEnd_20430 := by exact prefixLift 20430
  have htrace : WordTrace (prefixWord ++ tailWord_20430) baseStart_20430 baseEnd_20430 := by
    simpa [prefixWord, tailWord_20430, baseEnd_20430] using wordTrace_append hprefix tailTrace_20430
  have hstable : (prefixWord ++ tailWord_20430).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20430).length < 2 ^ (prefixWord ++ tailWord_20430).sum := by decide
  have hdescent : baseEnd_20430 < baseStart_20430 := by decide
  rcases family_descends (prefixWord ++ tailWord_20430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20432 : List Nat := [2, 1, 1, 1, 1, 2, 5, 6]
def baseStart_20432 : Nat := 118140960795 + 20432 * 2 ^ 59
def prefixEnd_20432 : Nat := 4983230072969 + 3 ^ 40 * 20432 * 2
def baseEnd_20432 : Nat := 6217147693492914610987

theorem tailTrace_20432 : CollatzResearch.WordTrace tailWord_20432 prefixEnd_20432 6217147693492914610987 := by
  unfold tailWord_20432
  simp only [CollatzResearch.WordTrace]
  refine ⟨372608130992914176447775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 496810841323885568597033 372608130992914176447775)
  ·
    refine ⟨558912196489371264671663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 372608130992914176447775 558912196489371264671663)
    ·
      refine ⟨838368294734056897007495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 558912196489371264671663 838368294734056897007495)
      ·
        refine ⟨1257552442101085345511243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 838368294734056897007495 1257552442101085345511243)
        ·
          refine ⟨1886328663151628018266865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1257552442101085345511243 1886328663151628018266865)
          ·
            refine ⟨1414746497363721013700149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1886328663151628018266865 1414746497363721013700149)
            ·
              refine ⟨132632484127848845034389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1414746497363721013700149 132632484127848845034389)
              ·
                refine ⟨6217147693492914610987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 132632484127848845034389 6217147693492914610987)
                ·
                  rfl

theorem cell19_20432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 6].length) (baseStart_20432 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_20432 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_20432 prefixEnd_20432 := by exact prefixLift 20432
  have htrace : WordTrace (prefixWord ++ tailWord_20432) baseStart_20432 baseEnd_20432 := by
    simpa [prefixWord, tailWord_20432, baseEnd_20432] using wordTrace_append hprefix tailTrace_20432
  have hstable : (prefixWord ++ tailWord_20432).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20432).length < 2 ^ (prefixWord ++ tailWord_20432).sum := by decide
  have hdescent : baseEnd_20432 < baseStart_20432 := by decide
  rcases family_descends (prefixWord ++ tailWord_20432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20487 : List Nat := [1, 1, 4, 3, 1, 2, 3, 4]
def baseStart_20487 : Nat := 118140960795 + 20487 * 2 ^ 59
def prefixEnd_20487 : Nat := 4983230072969 + 3 ^ 40 * 20487 * 2
def baseEnd_20487 : Nat := 6233883359269083388615

theorem tailTrace_20487 : CollatzResearch.WordTrace tailWord_20487 prefixEnd_20487 6233883359269083388615 := by
  unfold tailWord_20487
  simp only [CollatzResearch.WordTrace]
  refine ⟨747222276786572746147715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 498148184524381830765143 747222276786572746147715)
  ·
    refine ⟨1120833415179859119221573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 747222276786572746147715 1120833415179859119221573)
    ·
      refine ⟨210156265346223584854045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1120833415179859119221573 210156265346223584854045)
      ·
        refine ⟨78808599504833844320267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210156265346223584854045 78808599504833844320267)
        ·
          refine ⟨118212899257250766480401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78808599504833844320267 118212899257250766480401)
          ·
            refine ⟨88659674442938074860301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118212899257250766480401 88659674442938074860301)
            ·
              refine ⟨33247377916101778072613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88659674442938074860301 33247377916101778072613)
              ·
                refine ⟨6233883359269083388615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33247377916101778072613 6233883359269083388615)
                ·
                  rfl

theorem cell19_20487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 4].length) (baseStart_20487 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_20487 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_20487 prefixEnd_20487 := by exact prefixLift 20487
  have htrace : WordTrace (prefixWord ++ tailWord_20487) baseStart_20487 baseEnd_20487 := by
    simpa [prefixWord, tailWord_20487, baseEnd_20487] using wordTrace_append hprefix tailTrace_20487
  have hstable : (prefixWord ++ tailWord_20487).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20487).length < 2 ^ (prefixWord ++ tailWord_20487).sum := by decide
  have hdescent : baseEnd_20487 < baseStart_20487 := by decide
  rcases family_descends (prefixWord ++ tailWord_20487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20500 : List Nat := [2, 4, 3, 2, 1, 1, 3, 3]
def baseStart_20500 : Nat := 118140960795 + 20500 * 2 ^ 59
def prefixEnd_20500 : Nat := 4983230072969 + 3 ^ 40 * 20500 * 2
def baseEnd_20500 : Nat := 6237839062088905099691

theorem tailTrace_20500 : CollatzResearch.WordTrace tailWord_20500 prefixEnd_20500 6237839062088905099691 := by
  unfold tailWord_20500
  simp only [CollatzResearch.WordTrace]
  refine ⟨373848212869737983185477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 498464283826317310913969 373848212869737983185477)
  ·
    refine ⟨70096539913075871847277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 373848212869737983185477 70096539913075871847277)
    ·
      refine ⟨26286202467403451942729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70096539913075871847277 26286202467403451942729)
      ·
        refine ⟨19714651850552588957047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26286202467403451942729 19714651850552588957047)
        ·
          refine ⟨29571977775828883435571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19714651850552588957047 29571977775828883435571)
          ·
            refine ⟨44357966663743325153357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29571977775828883435571 44357966663743325153357)
            ·
              refine ⟨16634237498903746932509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44357966663743325153357 16634237498903746932509)
              ·
                refine ⟨6237839062088905099691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16634237498903746932509 6237839062088905099691)
                ·
                  rfl

theorem cell19_20500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 3].length) (baseStart_20500 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_20500 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_20500 prefixEnd_20500 := by exact prefixLift 20500
  have htrace : WordTrace (prefixWord ++ tailWord_20500) baseStart_20500 baseEnd_20500 := by
    simpa [prefixWord, tailWord_20500, baseEnd_20500] using wordTrace_append hprefix tailTrace_20500
  have hstable : (prefixWord ++ tailWord_20500).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20500).length < 2 ^ (prefixWord ++ tailWord_20500).sum := by decide
  have hdescent : baseEnd_20500 < baseStart_20500 := by decide
  rcases family_descends (prefixWord ++ tailWord_20500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20578 : List Nat := [3, 3, 2, 2, 3, 1, 5]
def baseStart_20578 : Nat := 118140960795 + 20578 * 2 ^ 59
def prefixEnd_20578 : Nat := 4983230072969 + 3 ^ 40 * 20578 * 2
def baseEnd_20578 : Nat := 2087191093002611788715

theorem tailTrace_20578 : CollatzResearch.WordTrace tailWord_20578 prefixEnd_20578 2087191093002611788715 := by
  unfold tailWord_20578
  simp only [CollatzResearch.WordTrace]
  refine ⟨187635329864223821927597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 500360879637930191806925 187635329864223821927597)
  ·
    refine ⟨70363248699083933222849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187635329864223821927597 70363248699083933222849)
    ·
      refine ⟨52772436524312949917137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70363248699083933222849 52772436524312949917137)
      ·
        refine ⟨39579327393234712437853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52772436524312949917137 39579327393234712437853)
        ·
          refine ⟨14842247772463017164195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39579327393234712437853 14842247772463017164195)
          ·
            refine ⟨22263371658694525746293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14842247772463017164195 22263371658694525746293)
            ·
              refine ⟨2087191093002611788715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22263371658694525746293 2087191093002611788715)
              ·
                rfl

theorem cell19_20578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 5].length) (baseStart_20578 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_20578 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_20578 prefixEnd_20578 := by exact prefixLift 20578
  have htrace : WordTrace (prefixWord ++ tailWord_20578) baseStart_20578 baseEnd_20578 := by
    simpa [prefixWord, tailWord_20578, baseEnd_20578] using wordTrace_append hprefix tailTrace_20578
  have hstable : (prefixWord ++ tailWord_20578).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20578).length < 2 ^ (prefixWord ++ tailWord_20578).sum := by decide
  have hdescent : baseEnd_20578 < baseStart_20578 := by decide
  rcases family_descends (prefixWord ++ tailWord_20578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20601 : List Nat := [1, 2, 1, 3, 4, 2, 2, 4]
def baseStart_20601 : Nat := 118140960795 + 20601 * 2 ^ 59
def prefixEnd_20601 : Nat := 4983230072969 + 3 ^ 40 * 20601 * 2
def baseEnd_20601 : Nat := 6268571830150596854971

theorem tailTrace_20601 : CollatzResearch.WordTrace tailWord_20601 prefixEnd_20601 6268571830150596854971 := by
  unfold tailWord_20601
  simp only [CollatzResearch.WordTrace]
  refine ⟨751380198373570215797657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 500920132249046810531771 751380198373570215797657)
  ·
    refine ⟨563535148780177661848243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 751380198373570215797657 563535148780177661848243)
    ·
      refine ⟨845302723170266492772365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 563535148780177661848243 845302723170266492772365)
      ·
        refine ⟨316988521188849934789637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 845302723170266492772365 316988521188849934789637)
        ·
          refine ⟨59435347722909362773057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 316988521188849934789637 59435347722909362773057)
          ·
            refine ⟨44576510792182022079793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59435347722909362773057 44576510792182022079793)
            ·
              refine ⟨33432383094136516559845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44576510792182022079793 33432383094136516559845)
              ·
                refine ⟨6268571830150596854971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33432383094136516559845 6268571830150596854971)
                ·
                  rfl

theorem cell19_20601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 4].length) (baseStart_20601 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_20601 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_20601 prefixEnd_20601 := by exact prefixLift 20601
  have htrace : WordTrace (prefixWord ++ tailWord_20601) baseStart_20601 baseEnd_20601 := by
    simpa [prefixWord, tailWord_20601, baseEnd_20601] using wordTrace_append hprefix tailTrace_20601
  have hstable : (prefixWord ++ tailWord_20601).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20601).length < 2 ^ (prefixWord ++ tailWord_20601).sum := by decide
  have hdescent : baseEnd_20601 < baseStart_20601 := by decide
  rcases family_descends (prefixWord ++ tailWord_20601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20641 : List Nat := [1, 2, 3, 3, 1, 9]
def baseStart_20641 : Nat := 118140960795 + 20641 * 2 ^ 59
def prefixEnd_20641 : Nat := 4983230072969 + 3 ^ 40 * 20641 * 2
def baseEnd_20641 : Nat := 697860358160261773997

theorem tailTrace_20641 : CollatzResearch.WordTrace tailWord_20641 prefixEnd_20641 697860358160261773997 := by
  unfold tailWord_20641
  simp only [CollatzResearch.WordTrace]
  refine ⟨752839118228657047253777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 501892745485771364835851 752839118228657047253777)
  ·
    refine ⟨564629338671492785440333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 752839118228657047253777 564629338671492785440333)
    ·
      refine ⟨211736002001809794540125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 564629338671492785440333 211736002001809794540125)
      ·
        refine ⟨79401000750678672952547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 211736002001809794540125 79401000750678672952547)
        ·
          refine ⟨119101501126018009428821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79401000750678672952547 119101501126018009428821)
          ·
            refine ⟨697860358160261773997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 119101501126018009428821 697860358160261773997)
            ·
              rfl

theorem cell19_20641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 9].length) (baseStart_20641 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_20641 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_20641 prefixEnd_20641 := by exact prefixLift 20641
  have htrace : WordTrace (prefixWord ++ tailWord_20641) baseStart_20641 baseEnd_20641 := by
    simpa [prefixWord, tailWord_20641, baseEnd_20641] using wordTrace_append hprefix tailTrace_20641
  have hstable : (prefixWord ++ tailWord_20641).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20641).length < 2 ^ (prefixWord ++ tailWord_20641).sum := by decide
  have hdescent : baseEnd_20641 < baseStart_20641 := by decide
  rcases family_descends (prefixWord ++ tailWord_20641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20673 : List Nat := [1, 2, 6, 1, 2, 1, 3, 3]
def baseStart_20673 : Nat := 118140960795 + 20673 * 2 ^ 59
def prefixEnd_20673 : Nat := 4983230072969 + 3 ^ 40 * 20673 * 2
def baseEnd_20673 : Nat := 6290480338075763254775

theorem tailTrace_20673 : CollatzResearch.WordTrace tailWord_20673 prefixEnd_20673 6290480338075763254775 := by
  unfold tailWord_20673
  simp only [CollatzResearch.WordTrace]
  refine ⟨754006254112726512418673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 502670836075151008279115 754006254112726512418673)
  ·
    refine ⟨565504690584544884314005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 754006254112726512418673 565504690584544884314005)
    ·
      refine ⟨26508032371150541452219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 565504690584544884314005 26508032371150541452219)
      ·
        refine ⟨39762048556725812178329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26508032371150541452219 39762048556725812178329)
        ·
          refine ⟨29821536417544359133747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39762048556725812178329 29821536417544359133747)
          ·
            refine ⟨44732304626316538700621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29821536417544359133747 44732304626316538700621)
            ·
              refine ⟨16774614234868702012733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44732304626316538700621 16774614234868702012733)
              ·
                refine ⟨6290480338075763254775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16774614234868702012733 6290480338075763254775)
                ·
                  rfl

theorem cell19_20673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 3].length) (baseStart_20673 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_20673 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_20673 prefixEnd_20673 := by exact prefixLift 20673
  have htrace : WordTrace (prefixWord ++ tailWord_20673) baseStart_20673 baseEnd_20673 := by
    simpa [prefixWord, tailWord_20673, baseEnd_20673] using wordTrace_append hprefix tailTrace_20673
  have hstable : (prefixWord ++ tailWord_20673).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20673).length < 2 ^ (prefixWord ++ tailWord_20673).sum := by decide
  have hdescent : baseEnd_20673 < baseStart_20673 := by decide
  rcases family_descends (prefixWord ++ tailWord_20673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20694 : List Nat := [5, 2, 1, 2, 1, 2, 6]
def baseStart_20694 : Nat := 118140960795 + 20694 * 2 ^ 59
def prefixEnd_20694 : Nat := 4983230072969 + 3 ^ 40 * 20694 * 2
def baseEnd_20694 : Nat := 2098956773184645596017

theorem tailTrace_20694 : CollatzResearch.WordTrace tailWord_20694 prefixEnd_20694 2098956773184645596017 := by
  unfold tailWord_20694
  simp only [CollatzResearch.WordTrace]
  refine ⟨47173261689790443683321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 503181458024431399288757 47173261689790443683321)
  ·
    refine ⟨35379946267342832762491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47173261689790443683321 35379946267342832762491)
    ·
      refine ⟨53069919401014249143737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35379946267342832762491 53069919401014249143737)
      ·
        refine ⟨39802439550760686857803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53069919401014249143737 39802439550760686857803)
        ·
          refine ⟨59703659326141030286705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39802439550760686857803 59703659326141030286705)
          ·
            refine ⟨44777744494605772715029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59703659326141030286705 44777744494605772715029)
            ·
              refine ⟨2098956773184645596017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 44777744494605772715029 2098956773184645596017)
              ·
                rfl

theorem cell19_20694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 6].length) (baseStart_20694 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_20694 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_20694 prefixEnd_20694 := by exact prefixLift 20694
  have htrace : WordTrace (prefixWord ++ tailWord_20694) baseStart_20694 baseEnd_20694 := by
    simpa [prefixWord, tailWord_20694, baseEnd_20694] using wordTrace_append hprefix tailTrace_20694
  have hstable : (prefixWord ++ tailWord_20694).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20694).length < 2 ^ (prefixWord ++ tailWord_20694).sum := by decide
  have hdescent : baseEnd_20694 < baseStart_20694 := by decide
  rcases family_descends (prefixWord ++ tailWord_20694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20732 : List Nat := [2, 2, 2, 1, 4, 3, 2, 3]
def baseStart_20732 : Nat := 118140960795 + 20732 * 2 ^ 59
def prefixEnd_20732 : Nat := 4983230072969 + 3 ^ 40 * 20732 * 2
def baseEnd_20732 : Nat := 6308433143181107943503

theorem tailTrace_20732 : CollatzResearch.WordTrace tailWord_20732 prefixEnd_20732 6308433143181107943503 := by
  unfold tailWord_20732
  simp only [CollatzResearch.WordTrace]
  refine ⟨378079080449489794408225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 504105440599319725877633 378079080449489794408225)
  ·
    refine ⟨283559310337117345806169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 378079080449489794408225 283559310337117345806169)
    ·
      refine ⟨212669482752838009354627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283559310337117345806169 212669482752838009354627)
      ·
        refine ⟨319004224129257014031941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212669482752838009354627 319004224129257014031941)
        ·
          refine ⟨59813292024235690130989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 319004224129257014031941 59813292024235690130989)
          ·
            refine ⟨22429984509088383799121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59813292024235690130989 22429984509088383799121)
            ·
              refine ⟨16822488381816287849341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22429984509088383799121 16822488381816287849341)
              ·
                refine ⟨6308433143181107943503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16822488381816287849341 6308433143181107943503)
                ·
                  rfl

theorem cell19_20732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 3].length) (baseStart_20732 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_20732 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_20732 prefixEnd_20732 := by exact prefixLift 20732
  have htrace : WordTrace (prefixWord ++ tailWord_20732) baseStart_20732 baseEnd_20732 := by
    simpa [prefixWord, tailWord_20732, baseEnd_20732] using wordTrace_append hprefix tailTrace_20732
  have hstable : (prefixWord ++ tailWord_20732).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20732).length < 2 ^ (prefixWord ++ tailWord_20732).sum := by decide
  have hdescent : baseEnd_20732 < baseStart_20732 := by decide
  rcases family_descends (prefixWord ++ tailWord_20732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20734 : List Nat := [4, 2, 2, 1, 1, 1, 3, 5]
def baseStart_20734 : Nat := 118140960795 + 20734 * 2 ^ 59
def prefixEnd_20734 : Nat := 4983230072969 + 3 ^ 40 * 20734 * 2
def baseEnd_20734 : Nat := 6309041712845695899053

theorem tailTrace_20734 : CollatzResearch.WordTrace tailWord_20734 prefixEnd_20734 6309041712845695899053 := by
  unfold tailWord_20734
  simp only [CollatzResearch.WordTrace]
  refine ⟨94528888361466741298657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 504154071261155953592837 94528888361466741298657)
  ·
    refine ⟨70896666271100055973993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94528888361466741298657 70896666271100055973993)
    ·
      refine ⟨53172499703325041980495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70896666271100055973993 53172499703325041980495)
      ·
        refine ⟨79758749554987562970743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53172499703325041980495 79758749554987562970743)
        ·
          refine ⟨119638124332481344456115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79758749554987562970743 119638124332481344456115)
          ·
            refine ⟨179457186498722016684173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119638124332481344456115 179457186498722016684173)
            ·
              refine ⟨67296444937020756256565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 179457186498722016684173 67296444937020756256565)
              ·
                refine ⟨6309041712845695899053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67296444937020756256565 6309041712845695899053)
                ·
                  rfl

theorem cell19_20734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_20734 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_20734 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_20734 prefixEnd_20734 := by exact prefixLift 20734
  have htrace : WordTrace (prefixWord ++ tailWord_20734) baseStart_20734 baseEnd_20734 := by
    simpa [prefixWord, tailWord_20734, baseEnd_20734] using wordTrace_append hprefix tailTrace_20734
  have hstable : (prefixWord ++ tailWord_20734).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20734).length < 2 ^ (prefixWord ++ tailWord_20734).sum := by decide
  have hdescent : baseEnd_20734 < baseStart_20734 := by decide
  rcases family_descends (prefixWord ++ tailWord_20734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20772 : List Nat := [2, 3, 1, 3, 1, 3, 2, 4]
def baseStart_20772 : Nat := 118140960795 + 20772 * 2 ^ 59
def prefixEnd_20772 : Nat := 4983230072969 + 3 ^ 40 * 20772 * 2
def baseEnd_20772 : Nat := 6320604536472867054505

theorem tailTrace_20772 : CollatzResearch.WordTrace tailWord_20772 prefixEnd_20772 6320604536472867054505 := by
  unfold tailWord_20772
  simp only [CollatzResearch.WordTrace]
  refine ⟨378808540377033210136285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 505078053836044280181713 378808540377033210136285)
  ·
    refine ⟨142053202641387453801107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 378808540377033210136285 142053202641387453801107)
    ·
      refine ⟨213079803962081180701661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142053202641387453801107 213079803962081180701661)
      ·
        refine ⟨79904926485780442763123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 213079803962081180701661 79904926485780442763123)
        ·
          refine ⟨119857389728670664144685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79904926485780442763123 119857389728670664144685)
          ·
            refine ⟨44946521148251499054257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119857389728670664144685 44946521148251499054257)
            ·
              refine ⟨33709890861188624290693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44946521148251499054257 33709890861188624290693)
              ·
                refine ⟨6320604536472867054505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33709890861188624290693 6320604536472867054505)
                ·
                  rfl

theorem cell19_20772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 4].length) (baseStart_20772 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_20772 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_20772 prefixEnd_20772 := by exact prefixLift 20772
  have htrace : WordTrace (prefixWord ++ tailWord_20772) baseStart_20772 baseEnd_20772 := by
    simpa [prefixWord, tailWord_20772, baseEnd_20772] using wordTrace_append hprefix tailTrace_20772
  have hstable : (prefixWord ++ tailWord_20772).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20772).length < 2 ^ (prefixWord ++ tailWord_20772).sum := by decide
  have hdescent : baseEnd_20772 < baseStart_20772 := by decide
  rcases family_descends (prefixWord ++ tailWord_20772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20831 : List Nat := [1, 1, 2, 3, 1, 2, 5, 4]
def baseStart_20831 : Nat := 118140960795 + 20831 * 2 ^ 59
def prefixEnd_20831 : Nat := 4983230072969 + 3 ^ 40 * 20831 * 2
def baseEnd_20831 : Nat := 6338557341578211743233

theorem tailTrace_20831 : CollatzResearch.WordTrace tailWord_20831 prefixEnd_20831 6338557341578211743233 := by
  unfold tailWord_20831
  simp only [CollatzResearch.WordTrace]
  refine ⟨759768987540319496670347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 506512658360212997780231 759768987540319496670347)
  ·
    refine ⟨1139653481310479245005521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 759768987540319496670347 1139653481310479245005521)
    ·
      refine ⟨854740110982859433754141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1139653481310479245005521 854740110982859433754141)
      ·
        refine ⟨320527541618572287657803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 854740110982859433754141 320527541618572287657803)
        ·
          refine ⟨480791312427858431486705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 320527541618572287657803 480791312427858431486705)
          ·
            refine ⟨360593484320893823615029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 480791312427858431486705 360593484320893823615029)
            ·
              refine ⟨33805639155083795963909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 360593484320893823615029 33805639155083795963909)
              ·
                refine ⟨6338557341578211743233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33805639155083795963909 6338557341578211743233)
                ·
                  rfl

theorem cell19_20831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 4].length) (baseStart_20831 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_20831 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_20831 prefixEnd_20831 := by exact prefixLift 20831
  have htrace : WordTrace (prefixWord ++ tailWord_20831) baseStart_20831 baseEnd_20831 := by
    simpa [prefixWord, tailWord_20831, baseEnd_20831] using wordTrace_append hprefix tailTrace_20831
  have hstable : (prefixWord ++ tailWord_20831).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20831).length < 2 ^ (prefixWord ++ tailWord_20831).sum := by decide
  have hdescent : baseEnd_20831 < baseStart_20831 := by decide
  rcases family_descends (prefixWord ++ tailWord_20831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20848 : List Nat := [2, 1, 1, 1, 4, 4, 3, 3]
def baseStart_20848 : Nat := 118140960795 + 20848 * 2 ^ 59
def prefixEnd_20848 : Nat := 4983230072969 + 3 ^ 40 * 20848 * 2
def baseEnd_20848 : Nat := 6343730183727209365409

theorem tailTrace_20848 : CollatzResearch.WordTrace tailWord_20848 prefixEnd_20848 6343730183727209365409 := by
  unfold tailWord_20848
  simp only [CollatzResearch.WordTrace]
  refine ⟨380194514239365700019599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 506926018985820933359465 380194514239365700019599)
  ·
    refine ⟨570291771359048550029399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 380194514239365700019599 570291771359048550029399)
    ·
      refine ⟨855437657038572825044099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 570291771359048550029399 855437657038572825044099)
      ·
        refine ⟨1283156485557859237566149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 855437657038572825044099 1283156485557859237566149)
        ·
          refine ⟨240591841042098607043653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1283156485557859237566149 240591841042098607043653)
          ·
            refine ⟨45110970195393488820685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 240591841042098607043653 45110970195393488820685)
            ·
              refine ⟨16916613823272558307757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45110970195393488820685 16916613823272558307757)
              ·
                refine ⟨6343730183727209365409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16916613823272558307757 6343730183727209365409)
                ·
                  rfl

theorem cell19_20848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 3].length) (baseStart_20848 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_20848 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_20848 prefixEnd_20848 := by exact prefixLift 20848
  have htrace : WordTrace (prefixWord ++ tailWord_20848) baseStart_20848 baseEnd_20848 := by
    simpa [prefixWord, tailWord_20848, baseEnd_20848] using wordTrace_append hprefix tailTrace_20848
  have hstable : (prefixWord ++ tailWord_20848).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20848).length < 2 ^ (prefixWord ++ tailWord_20848).sum := by decide
  have hdescent : baseEnd_20848 < baseStart_20848 := by decide
  rcases family_descends (prefixWord ++ tailWord_20848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20903 : List Nat := [1, 1, 6, 1, 1, 4, 2, 3]
def baseStart_20903 : Nat := 118140960795 + 20903 * 2 ^ 59
def prefixEnd_20903 : Nat := 4983230072969 + 3 ^ 40 * 20903 * 2
def baseEnd_20903 : Nat := 6360465849503378143037

theorem tailTrace_20903 : CollatzResearch.WordTrace tailWord_20903 prefixEnd_20903 6360465849503378143037 := by
  unfold tailWord_20903
  simp only [CollatzResearch.WordTrace]
  refine ⟨762395043279475793291363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 508263362186317195527575 762395043279475793291363)
  ·
    refine ⟨1143592564919213689937045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 762395043279475793291363 1143592564919213689937045)
    ·
      refine ⟨53605901480588141715799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1143592564919213689937045 53605901480588141715799)
      ·
        refine ⟨80408852220882212573699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53605901480588141715799 80408852220882212573699)
        ·
          refine ⟨120613278331323318860549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80408852220882212573699 120613278331323318860549)
          ·
            refine ⟨22614989687123122286353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 120613278331323318860549 22614989687123122286353)
            ·
              refine ⟨16961242265342341714765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22614989687123122286353 16961242265342341714765)
              ·
                refine ⟨6360465849503378143037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16961242265342341714765 6360465849503378143037)
                ·
                  rfl

theorem cell19_20903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 3].length) (baseStart_20903 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_20903 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_20903 prefixEnd_20903 := by exact prefixLift 20903
  have htrace : WordTrace (prefixWord ++ tailWord_20903) baseStart_20903 baseEnd_20903 := by
    simpa [prefixWord, tailWord_20903, baseEnd_20903] using wordTrace_append hprefix tailTrace_20903
  have hstable : (prefixWord ++ tailWord_20903).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20903).length < 2 ^ (prefixWord ++ tailWord_20903).sum := by decide
  have hdescent : baseEnd_20903 < baseStart_20903 := by decide
  rcases family_descends (prefixWord ++ tailWord_20903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20924 : List Nat := [2, 2, 2, 4, 1, 3, 5]
def baseStart_20924 : Nat := 118140960795 + 20924 * 2 ^ 59
def prefixEnd_20924 : Nat := 4983230072969 + 3 ^ 40 * 20924 * 2
def baseEnd_20924 : Nat := 2122285276993850558771

theorem tailTrace_20924 : CollatzResearch.WordTrace tailWord_20924 prefixEnd_20924 2122285276993850558771 := by
  unfold tailWord_20924
  simp only [CollatzResearch.WordTrace]
  refine ⟨381580488101698189902913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 508773984135597586537217 381580488101698189902913)
  ·
    refine ⟨286185366076273642427185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 381580488101698189902913 286185366076273642427185)
    ·
      refine ⟨214639024557205231820389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286185366076273642427185 214639024557205231820389)
      ·
        refine ⟨40244817104475980966323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 214639024557205231820389 40244817104475980966323)
        ·
          refine ⟨60367225656713971449485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40244817104475980966323 60367225656713971449485)
          ·
            refine ⟨22637709621267739293557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60367225656713971449485 22637709621267739293557)
            ·
              refine ⟨2122285276993850558771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22637709621267739293557 2122285276993850558771)
              ·
                rfl

theorem cell19_20924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 5].length) (baseStart_20924 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_20924 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_20924 prefixEnd_20924 := by exact prefixLift 20924
  have htrace : WordTrace (prefixWord ++ tailWord_20924) baseStart_20924 baseEnd_20924 := by
    simpa [prefixWord, tailWord_20924, baseEnd_20924] using wordTrace_append hprefix tailTrace_20924
  have hstable : (prefixWord ++ tailWord_20924).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20924).length < 2 ^ (prefixWord ++ tailWord_20924).sum := by decide
  have hdescent : baseEnd_20924 < baseStart_20924 := by decide
  rcases family_descends (prefixWord ++ tailWord_20924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20926 : List Nat := [4, 2, 1, 1, 1, 1, 9]
def baseStart_20926 : Nat := 118140960795 + 20926 * 2 ^ 59
def prefixEnd_20926 : Nat := 4983230072969 + 3 ^ 40 * 20926 * 2
def baseEnd_20926 : Nat := 2122488133548713210621

theorem tailTrace_20926 : CollatzResearch.WordTrace tailWord_20926 prefixEnd_20926 2122488133548713210621 := by
  unfold tailWord_20926
  simp only [CollatzResearch.WordTrace]
  refine ⟨95404240274518840172329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 508822614797433814252421 95404240274518840172329)
  ·
    refine ⟨71553180205889130129247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95404240274518840172329 71553180205889130129247)
    ·
      refine ⟨107329770308833695193871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71553180205889130129247 107329770308833695193871)
      ·
        refine ⟨160994655463250542790807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107329770308833695193871 160994655463250542790807)
        ·
          refine ⟨241491983194875814186211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160994655463250542790807 241491983194875814186211)
          ·
            refine ⟨362237974792313721279317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241491983194875814186211 362237974792313721279317)
            ·
              refine ⟨2122488133548713210621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 362237974792313721279317 2122488133548713210621)
              ·
                rfl

theorem cell19_20926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 9].length) (baseStart_20926 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_20926 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_20926 prefixEnd_20926 := by exact prefixLift 20926
  have htrace : WordTrace (prefixWord ++ tailWord_20926) baseStart_20926 baseEnd_20926 := by
    simpa [prefixWord, tailWord_20926, baseEnd_20926] using wordTrace_append hprefix tailTrace_20926
  have hstable : (prefixWord ++ tailWord_20926).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20926).length < 2 ^ (prefixWord ++ tailWord_20926).sum := by decide
  have hdescent : baseEnd_20926 < baseStart_20926 := by decide
  rcases family_descends (prefixWord ++ tailWord_20926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_20981 : List Nat := [1, 3, 5, 1, 2, 7]
def baseStart_20981 : Nat := 118140960795 + 20981 * 2 ^ 59
def prefixEnd_20981 : Nat := 4983230072969 + 3 ^ 40 * 20981 * 2
def baseEnd_20981 : Nat := 709355562935812045499

theorem tailTrace_20981 : CollatzResearch.WordTrace tailWord_20981 prefixEnd_20981 709355562935812045499 := by
  unfold tailWord_20981
  simp only [CollatzResearch.WordTrace]
  refine ⟨765239936996895114630797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 510159957997930076420531 765239936996895114630797)
  ·
    refine ⟨286964976373835667986549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 765239936996895114630797 286964976373835667986549)
    ·
      refine ⟨26902966535047093873739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 286964976373835667986549 26902966535047093873739)
      ·
        refine ⟨40354449802570640810609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26902966535047093873739 40354449802570640810609)
        ·
          refine ⟨30265837351927980607957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40354449802570640810609 30265837351927980607957)
          ·
            refine ⟨709355562935812045499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 30265837351927980607957 709355562935812045499)
            ·
              rfl

theorem cell19_20981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 7].length) (baseStart_20981 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_20981 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_20981 prefixEnd_20981 := by exact prefixLift 20981
  have htrace : WordTrace (prefixWord ++ tailWord_20981) baseStart_20981 baseEnd_20981 := by
    simpa [prefixWord, tailWord_20981, baseEnd_20981] using wordTrace_append hprefix tailTrace_20981
  have hstable : (prefixWord ++ tailWord_20981).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_20981).length < 2 ^ (prefixWord ++ tailWord_20981).sum := by decide
  have hdescent : baseEnd_20981 < baseStart_20981 := by decide
  rcases family_descends (prefixWord ++ tailWord_20981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21038 : List Nat := [4, 1, 3, 1, 3, 1, 6]
def baseStart_21038 : Nat := 118140960795 + 21038 * 2 ^ 59
def prefixEnd_21038 : Nat := 4983230072969 + 3 ^ 40 * 21038 * 2
def baseEnd_21038 : Nat := 2133848100621021714223

theorem tailTrace_21038 : CollatzResearch.WordTrace tailWord_21038 prefixEnd_21038 2133848100621021714223 := by
  unfold tailWord_21038
  simp only [CollatzResearch.WordTrace]
  refine ⟨95914862223799231181971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 511545931860262566303845 95914862223799231181971)
  ·
    refine ⟨143872293335698846772957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95914862223799231181971 143872293335698846772957)
    ·
      refine ⟨53952110000887067539859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143872293335698846772957 53952110000887067539859)
      ·
        refine ⟨80928165001330601309789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53952110000887067539859 80928165001330601309789)
        ·
          refine ⟨30348061875498975491171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80928165001330601309789 30348061875498975491171)
          ·
            refine ⟨45522092813248463236757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30348061875498975491171 45522092813248463236757)
            ·
              refine ⟨2133848100621021714223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 45522092813248463236757 2133848100621021714223)
              ·
                rfl

theorem cell19_21038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 6].length) (baseStart_21038 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_21038 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_21038 prefixEnd_21038 := by exact prefixLift 21038
  have htrace : WordTrace (prefixWord ++ tailWord_21038) baseStart_21038 baseEnd_21038 := by
    simpa [prefixWord, tailWord_21038, baseEnd_21038] using wordTrace_append hprefix tailTrace_21038
  have hstable : (prefixWord ++ tailWord_21038).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21038).length < 2 ^ (prefixWord ++ tailWord_21038).sum := by decide
  have hdescent : baseEnd_21038 < baseStart_21038 := by decide
  rcases family_descends (prefixWord ++ tailWord_21038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21076 : List Nat := [2, 4, 1, 1, 1, 3, 4, 3]
def baseStart_21076 : Nat := 118140960795 + 21076 * 2 ^ 59
def prefixEnd_21076 : Nat := 4983230072969 + 3 ^ 40 * 21076 * 2
def baseEnd_21076 : Nat := 6413107125490236298121

theorem tailTrace_21076 : CollatzResearch.WordTrace tailWord_21076 prefixEnd_21076 6413107125490236298121 := by
  unfold tailWord_21076
  simp only [CollatzResearch.WordTrace]
  refine ⟨384352435826363169669541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 512469914435150892892721 384352435826363169669541)
  ·
    refine ⟨72066081717443094313039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 384352435826363169669541 72066081717443094313039)
    ·
      refine ⟨108099122576164641469559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72066081717443094313039 108099122576164641469559)
      ·
        refine ⟨162148683864246962204339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108099122576164641469559 162148683864246962204339)
        ·
          refine ⟨243223025796370443306509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162148683864246962204339 243223025796370443306509)
          ·
            refine ⟨91208634673638916239941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 243223025796370443306509 91208634673638916239941)
            ·
              refine ⟨17101619001307296794989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91208634673638916239941 17101619001307296794989)
              ·
                refine ⟨6413107125490236298121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17101619001307296794989 6413107125490236298121)
                ·
                  rfl

theorem cell19_21076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 3].length) (baseStart_21076 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_21076 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_21076 prefixEnd_21076 := by exact prefixLift 21076
  have htrace : WordTrace (prefixWord ++ tailWord_21076) baseStart_21076 baseEnd_21076 := by
    simpa [prefixWord, tailWord_21076, baseEnd_21076] using wordTrace_append hprefix tailTrace_21076
  have hstable : (prefixWord ++ tailWord_21076).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21076).length < 2 ^ (prefixWord ++ tailWord_21076).sum := by decide
  have hdescent : baseEnd_21076 < baseStart_21076 := by decide
  rcases family_descends (prefixWord ++ tailWord_21076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21169 : List Nat := [1, 2, 2, 6, 1, 2, 1, 4]
def baseStart_21169 : Nat := 118140960795 + 21169 * 2 ^ 59
def prefixEnd_21169 : Nat := 4983230072969 + 3 ^ 40 * 21169 * 2
def baseEnd_21169 : Nat := 6441405614893576231201

theorem tailTrace_21169 : CollatzResearch.WordTrace tailWord_21169 prefixEnd_21169 6441405614893576231201 := by
  unfold tailWord_21169
  simp only [CollatzResearch.WordTrace]
  refine ⟨772096860315803222474561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 514731240210535481649707 772096860315803222474561)
  ·
    refine ⟨579072645236852416855921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 772096860315803222474561 579072645236852416855921)
    ·
      refine ⟨434304483927639312641941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 579072645236852416855921 434304483927639312641941)
      ·
        refine ⟨20358022684108092780091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 434304483927639312641941 20358022684108092780091)
        ·
          refine ⟨30537034026162139170137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20358022684108092780091 30537034026162139170137)
          ·
            refine ⟨22902775519621604377603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30537034026162139170137 22902775519621604377603)
            ·
              refine ⟨34354163279432406566405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22902775519621604377603 34354163279432406566405)
              ·
                refine ⟨6441405614893576231201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34354163279432406566405 6441405614893576231201)
                ·
                  rfl

theorem cell19_21169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 4].length) (baseStart_21169 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_21169 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_21169 prefixEnd_21169 := by exact prefixLift 21169
  have htrace : WordTrace (prefixWord ++ tailWord_21169) baseStart_21169 baseEnd_21169 := by
    simpa [prefixWord, tailWord_21169, baseEnd_21169] using wordTrace_append hprefix tailTrace_21169
  have hstable : (prefixWord ++ tailWord_21169).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21169).length < 2 ^ (prefixWord ++ tailWord_21169).sum := by decide
  have hdescent : baseEnd_21169 < baseStart_21169 := by decide
  rcases family_descends (prefixWord ++ tailWord_21169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21232 : List Nat := [2, 1, 1, 1, 3, 1, 4, 6]
def baseStart_21232 : Nat := 118140960795 + 21232 * 2 ^ 59
def prefixEnd_21232 : Nat := 4983230072969 + 3 ^ 40 * 21232 * 2
def baseEnd_21232 : Nat := 6460575559328096831029

theorem tailTrace_21232 : CollatzResearch.WordTrace tailWord_21232 prefixEnd_21232 6460575559328096831029 := by
  unfold tailWord_21232
  simp only [CollatzResearch.WordTrace]
  refine ⟨387197329543782491008975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 516263106058376654678633 387197329543782491008975)
  ·
    refine ⟨580795994315673736513463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 387197329543782491008975 580795994315673736513463)
    ·
      refine ⟨871193991473510604770195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 580795994315673736513463 871193991473510604770195)
      ·
        refine ⟨1306790987210265907155293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 871193991473510604770195 1306790987210265907155293)
        ·
          refine ⟨490046620203849715183235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1306790987210265907155293 490046620203849715183235)
          ·
            refine ⟨735069930305774572774853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 490046620203849715183235 735069930305774572774853)
            ·
              refine ⟨137825611932332732395285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 735069930305774572774853 137825611932332732395285)
              ·
                refine ⟨6460575559328096831029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 137825611932332732395285 6460575559328096831029)
                ·
                  rfl

theorem cell19_21232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 6].length) (baseStart_21232 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_21232 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_21232 prefixEnd_21232 := by exact prefixLift 21232
  have htrace : WordTrace (prefixWord ++ tailWord_21232) baseStart_21232 baseEnd_21232 := by
    simpa [prefixWord, tailWord_21232, baseEnd_21232] using wordTrace_append hprefix tailTrace_21232
  have hstable : (prefixWord ++ tailWord_21232).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21232).length < 2 ^ (prefixWord ++ tailWord_21232).sum := by decide
  have hdescent : baseEnd_21232 < baseStart_21232 := by decide
  rcases family_descends (prefixWord ++ tailWord_21232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21325 : List Nat := [1, 6, 1, 2, 9]
def baseStart_21325 : Nat := 118140960795 + 21325 * 2 ^ 59
def prefixEnd_21325 : Nat := 4983230072969 + 3 ^ 40 * 21325 * 2
def baseEnd_21325 : Nat := 240328668471534694967

theorem tailTrace_21325 : CollatzResearch.WordTrace tailWord_21325 prefixEnd_21325 240328668471534694967 := by
  unfold tailWord_21325
  simp only [CollatzResearch.WordTrace]
  refine ⟨777786647750641865153429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 518524431833761243435619 777786647750641865153429)
  ·
    refine ⟨36458749113311337429067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 777786647750641865153429 36458749113311337429067)
    ·
      refine ⟨54688123669967006143601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36458749113311337429067 54688123669967006143601)
      ·
        refine ⟨41016092752475254607701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54688123669967006143601 41016092752475254607701)
        ·
          refine ⟨240328668471534694967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 41016092752475254607701 240328668471534694967)
          ·
            rfl

theorem cell19_21325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 9].length) (baseStart_21325 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_21325 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_21325 prefixEnd_21325 := by exact prefixLift 21325
  have htrace : WordTrace (prefixWord ++ tailWord_21325) baseStart_21325 baseEnd_21325 := by
    simpa [prefixWord, tailWord_21325, baseEnd_21325] using wordTrace_append hprefix tailTrace_21325
  have hstable : (prefixWord ++ tailWord_21325).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21325).length < 2 ^ (prefixWord ++ tailWord_21325).sum := by decide
  have hdescent : baseEnd_21325 < baseStart_21325 := by decide
  rcases family_descends (prefixWord ++ tailWord_21325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21378 : List Nat := [3, 4, 2, 2, 1, 1, 6]
def baseStart_21378 : Nat := 118140960795 + 21378 * 2 ^ 59
def prefixEnd_21378 : Nat := 4983230072969 + 3 ^ 40 * 21378 * 2
def baseEnd_21378 : Nat := 2168333714947672528729

theorem tailTrace_21378 : CollatzResearch.WordTrace tailWord_21378 prefixEnd_21378 2168333714947672528729 := by
  unfold tailWord_21378
  simp only [CollatzResearch.WordTrace]
  refine ⟨194929929139657979208197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 519813144372421277888525 194929929139657979208197)
  ·
    refine ⟨36549361713685871101537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 194929929139657979208197 36549361713685871101537)
    ·
      refine ⟨27412021285264403326153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36549361713685871101537 27412021285264403326153)
      ·
        refine ⟨20559015963948302494615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27412021285264403326153 20559015963948302494615)
        ·
          refine ⟨30838523945922453741923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20559015963948302494615 30838523945922453741923)
          ·
            refine ⟨46257785918883680612885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30838523945922453741923 46257785918883680612885)
            ·
              refine ⟨2168333714947672528729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 46257785918883680612885 2168333714947672528729)
              ·
                rfl

theorem cell19_21378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 6].length) (baseStart_21378 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_21378 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_21378 prefixEnd_21378 := by exact prefixLift 21378
  have htrace : WordTrace (prefixWord ++ tailWord_21378) baseStart_21378 baseEnd_21378 := by
    simpa [prefixWord, tailWord_21378, baseEnd_21378] using wordTrace_append hprefix tailTrace_21378
  have hstable : (prefixWord ++ tailWord_21378).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21378).length < 2 ^ (prefixWord ++ tailWord_21378).sum := by decide
  have hdescent : baseEnd_21378 < baseStart_21378 := by decide
  rcases family_descends (prefixWord ++ tailWord_21378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21437 : List Nat := [1, 4, 1, 2, 5, 1, 5]
def baseStart_21437 : Nat := 118140960795 + 21437 * 2 ^ 59
def prefixEnd_21437 : Nat := 4983230072969 + 3 ^ 40 * 21437 * 2
def baseEnd_21437 : Nat := 2174317983316120758305

theorem tailTrace_21437 : CollatzResearch.WordTrace tailWord_21437 prefixEnd_21437 2174317983316120758305 := by
  unfold tailWord_21437
  simp only [CollatzResearch.WordTrace]
  refine ⟨781871623344884993230565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 521247748896589995487043 781871623344884993230565)
  ·
    refine ⟨146600929377165936230731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 781871623344884993230565 146600929377165936230731)
    ·
      refine ⟨219901394065748904346097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146600929377165936230731 219901394065748904346097)
      ·
        refine ⟨164926045549311678259573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219901394065748904346097 164926045549311678259573)
        ·
          refine ⟨15461816770247969836835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 164926045549311678259573 15461816770247969836835)
          ·
            refine ⟨23192725155371954755253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15461816770247969836835 23192725155371954755253)
            ·
              refine ⟨2174317983316120758305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23192725155371954755253 2174317983316120758305)
              ·
                rfl

theorem cell19_21437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 5].length) (baseStart_21437 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_21437 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_21437 prefixEnd_21437 := by exact prefixLift 21437
  have htrace : WordTrace (prefixWord ++ tailWord_21437) baseStart_21437 baseEnd_21437 := by
    simpa [prefixWord, tailWord_21437, baseEnd_21437] using wordTrace_append hprefix tailTrace_21437
  have hstable : (prefixWord ++ tailWord_21437).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21437).length < 2 ^ (prefixWord ++ tailWord_21437).sum := by decide
  have hdescent : baseEnd_21437 < baseStart_21437 := by decide
  rcases family_descends (prefixWord ++ tailWord_21437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21458 : List Nat := [3, 2, 2, 3, 1, 1, 1, 6]
def baseStart_21458 : Nat := 118140960795 + 21458 * 2 ^ 59
def prefixEnd_21458 : Nat := 4983230072969 + 3 ^ 40 * 21458 * 2
def baseEnd_21458 : Nat := 6529343931426535808191

theorem tailTrace_21458 : CollatzResearch.WordTrace tailWord_21458 prefixEnd_21458 6529343931426535808191 := by
  unfold tailWord_21458
  simp only [CollatzResearch.WordTrace]
  refine ⟨195659389067201394936257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 521758370845870386496685 195659389067201394936257)
  ·
    refine ⟨146744541800401046202193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195659389067201394936257 146744541800401046202193)
    ·
      refine ⟨110058406350300784651645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146744541800401046202193 110058406350300784651645)
      ·
        refine ⟨41271902381362794244367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110058406350300784651645 41271902381362794244367)
        ·
          refine ⟨61907853572044191366551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41271902381362794244367 61907853572044191366551)
          ·
            refine ⟨92861780358066287049827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61907853572044191366551 92861780358066287049827)
            ·
              refine ⟨139292670537099430574741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92861780358066287049827 139292670537099430574741)
              ·
                refine ⟨6529343931426535808191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 139292670537099430574741 6529343931426535808191)
                ·
                  rfl

theorem cell19_21458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_21458 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_21458 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_21458 prefixEnd_21458 := by exact prefixLift 21458
  have htrace : WordTrace (prefixWord ++ tailWord_21458) baseStart_21458 baseEnd_21458 := by
    simpa [prefixWord, tailWord_21458, baseEnd_21458] using wordTrace_append hprefix tailTrace_21458
  have hstable : (prefixWord ++ tailWord_21458).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21458).length < 2 ^ (prefixWord ++ tailWord_21458).sum := by decide
  have hdescent : baseEnd_21458 < baseStart_21458 := by decide
  rcases family_descends (prefixWord ++ tailWord_21458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21492 : List Nat := [2, 6, 2, 1, 8]
def baseStart_21492 : Nat := 118140960795 + 21492 * 2 ^ 59
def prefixEnd_21492 : Nat := 4983230072969 + 3 ^ 40 * 21492 * 2
def baseEnd_21492 : Nat := 242210726508315964909

theorem tailTrace_21492 : CollatzResearch.WordTrace tailWord_21492 prefixEnd_21492 242210726508315964909 := by
  unfold tailWord_21492
  simp only [CollatzResearch.WordTrace]
  refine ⟨391938819072814693241365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 522585092097086257655153 391938819072814693241365)
  ·
    refine ⟨18372132144038188745689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 391938819072814693241365 18372132144038188745689)
    ·
      refine ⟨13779099108028641559267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18372132144038188745689 13779099108028641559267)
      ·
        refine ⟨20668648662042962338901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13779099108028641559267 20668648662042962338901)
        ·
          refine ⟨242210726508315964909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 20668648662042962338901 242210726508315964909)
          ·
            rfl

theorem cell19_21492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 8].length) (baseStart_21492 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_21492 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_21492 prefixEnd_21492 := by exact prefixLift 21492
  have htrace : WordTrace (prefixWord ++ tailWord_21492) baseStart_21492 baseEnd_21492 := by
    simpa [prefixWord, tailWord_21492, baseEnd_21492] using wordTrace_append hprefix tailTrace_21492
  have hstable : (prefixWord ++ tailWord_21492).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21492).length < 2 ^ (prefixWord ++ tailWord_21492).sum := by decide
  have hdescent : baseEnd_21492 < baseStart_21492 := by decide
  rcases family_descends (prefixWord ++ tailWord_21492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21515 : List Nat := [1, 1, 1, 1, 6, 4, 1, 4]
def baseStart_21515 : Nat := 118140960795 + 21515 * 2 ^ 59
def prefixEnd_21515 : Nat := 4983230072969 + 3 ^ 40 * 21515 * 2
def baseEnd_21515 : Nat := 6546688166867292541369

theorem tailTrace_21515 : CollatzResearch.WordTrace tailWord_21515 prefixEnd_21515 6546688166867292541369 := by
  unfold tailWord_21515
  simp only [CollatzResearch.WordTrace]
  refine ⟨784716517062304314569999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 523144344708202876379999 784716517062304314569999)
  ·
    refine ⟨1177074775593456471854999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 784716517062304314569999 1177074775593456471854999)
    ·
      refine ⟨1765612163390184707782499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1177074775593456471854999 1765612163390184707782499)
      ·
        refine ⟨2648418245085277061673749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1765612163390184707782499 2648418245085277061673749)
        ·
          refine ⟨124144605238372362265957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2648418245085277061673749 124144605238372362265957)
          ·
            refine ⟨23277113482194817924867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 124144605238372362265957 23277113482194817924867)
            ·
              refine ⟨34915670223292226887301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23277113482194817924867 34915670223292226887301)
              ·
                refine ⟨6546688166867292541369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34915670223292226887301 6546688166867292541369)
                ·
                  rfl

theorem cell19_21515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 4].length) (baseStart_21515 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_21515 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_21515 prefixEnd_21515 := by exact prefixLift 21515
  have htrace : WordTrace (prefixWord ++ tailWord_21515) baseStart_21515 baseEnd_21515 := by
    simpa [prefixWord, tailWord_21515, baseEnd_21515] using wordTrace_append hprefix tailTrace_21515
  have hstable : (prefixWord ++ tailWord_21515).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21515).length < 2 ^ (prefixWord ++ tailWord_21515).sum := by decide
  have hdescent : baseEnd_21515 < baseStart_21515 := by decide
  rcases family_descends (prefixWord ++ tailWord_21515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21532 : List Nat := [2, 2, 3, 1, 4, 1, 3, 3]
def baseStart_21532 : Nat := 118140960795 + 21532 * 2 ^ 59
def prefixEnd_21532 : Nat := 4983230072969 + 3 ^ 40 * 21532 * 2
def baseEnd_21532 : Nat := 6551861009016290163545

theorem tailTrace_21532 : CollatzResearch.WordTrace tailWord_21532 prefixEnd_21532 6551861009016290163545 := by
  unfold tailWord_21532
  simp only [CollatzResearch.WordTrace]
  refine ⟨392668279000358108969425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 523557705333810811959233 392668279000358108969425)
  ·
    refine ⟨294501209250268581727069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 392668279000358108969425 294501209250268581727069)
    ·
      refine ⟨110437953468850718147651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 294501209250268581727069 110437953468850718147651)
      ·
        refine ⟨165656930203276077221477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110437953468850718147651 165656930203276077221477)
        ·
          refine ⟨31060674413114264479027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 165656930203276077221477 31060674413114264479027)
          ·
            refine ⟨46591011619671396718541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31060674413114264479027 46591011619671396718541)
            ·
              refine ⟨17471629357376773769453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46591011619671396718541 17471629357376773769453)
              ·
                refine ⟨6551861009016290163545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17471629357376773769453 6551861009016290163545)
                ·
                  rfl

theorem cell19_21532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 3].length) (baseStart_21532 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_21532 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_21532 prefixEnd_21532 := by exact prefixLift 21532
  have htrace : WordTrace (prefixWord ++ tailWord_21532) baseStart_21532 baseEnd_21532 := by
    simpa [prefixWord, tailWord_21532, baseEnd_21532] using wordTrace_append hprefix tailTrace_21532
  have hstable : (prefixWord ++ tailWord_21532).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21532).length < 2 ^ (prefixWord ++ tailWord_21532).sum := by decide
  have hdescent : baseEnd_21532 < baseStart_21532 := by decide
  rcases family_descends (prefixWord ++ tailWord_21532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21608 : List Nat := [2, 1, 4, 4, 1, 2, 5]
def baseStart_21608 : Nat := 118140960795 + 21608 * 2 ^ 59
def prefixEnd_21608 : Nat := 4983230072969 + 3 ^ 40 * 21608 * 2
def baseEnd_21608 : Nat := 2191662218756877491483

theorem tailTrace_21608 : CollatzResearch.WordTrace tailWord_21608 prefixEnd_21608 2191662218756877491483 := by
  unfold tailWord_21608
  simp only [CollatzResearch.WordTrace]
  refine ⟨394054252862690598852739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 525405670483587465136985 394054252862690598852739)
  ·
    refine ⟨591081379294035898279109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 394054252862690598852739 591081379294035898279109)
    ·
      refine ⟨110827758617631730927333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 591081379294035898279109 110827758617631730927333)
      ·
        refine ⟨20780204740805949548875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110827758617631730927333 20780204740805949548875)
        ·
          refine ⟨31170307111208924323313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20780204740805949548875 31170307111208924323313)
          ·
            refine ⟨23377730333406693242485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31170307111208924323313 23377730333406693242485)
            ·
              refine ⟨2191662218756877491483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23377730333406693242485 2191662218756877491483)
              ·
                rfl

theorem cell19_21608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 5].length) (baseStart_21608 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_21608 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_21608 prefixEnd_21608 := by exact prefixLift 21608
  have htrace : WordTrace (prefixWord ++ tailWord_21608) baseStart_21608 baseEnd_21608 := by
    simpa [prefixWord, tailWord_21608, baseEnd_21608] using wordTrace_append hprefix tailTrace_21608
  have hstable : (prefixWord ++ tailWord_21608).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21608).length < 2 ^ (prefixWord ++ tailWord_21608).sum := by decide
  have hdescent : baseEnd_21608 < baseStart_21608 := by decide
  rcases family_descends (prefixWord ++ tailWord_21608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21610 : List Nat := [3, 1, 3, 2, 2, 3, 5]
def baseStart_21610 : Nat := 118140960795 + 21610 * 2 ^ 59
def prefixEnd_21610 : Nat := 4983230072969 + 3 ^ 40 * 21610 * 2
def baseEnd_21610 : Nat := 2191865075311740143333

theorem tailTrace_21610 : CollatzResearch.WordTrace tailWord_21610 prefixEnd_21610 2191865075311740143333 := by
  unfold tailWord_21610
  simp only [CollatzResearch.WordTrace]
  refine ⟨197045362929533884819571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 525454301145423692852189 197045362929533884819571)
  ·
    refine ⟨295568044394300827229357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197045362929533884819571 295568044394300827229357)
    ·
      refine ⟨110838016647862810211009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 295568044394300827229357 110838016647862810211009)
      ·
        refine ⟨83128512485897107658257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110838016647862810211009 83128512485897107658257)
        ·
          refine ⟨62346384364422830743693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83128512485897107658257 62346384364422830743693)
          ·
            refine ⟨23379894136658561528885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62346384364422830743693 23379894136658561528885)
            ·
              refine ⟨2191865075311740143333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23379894136658561528885 2191865075311740143333)
              ·
                rfl

theorem cell19_21610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 5].length) (baseStart_21610 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_21610 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_21610 prefixEnd_21610 := by exact prefixLift 21610
  have htrace : WordTrace (prefixWord ++ tailWord_21610) baseStart_21610 baseEnd_21610 := by
    simpa [prefixWord, tailWord_21610, baseEnd_21610] using wordTrace_append hprefix tailTrace_21610
  have hstable : (prefixWord ++ tailWord_21610).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21610).length < 2 ^ (prefixWord ++ tailWord_21610).sum := by decide
  have hdescent : baseEnd_21610 < baseStart_21610 := by decide
  rcases family_descends (prefixWord ++ tailWord_21610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21800 : List Nat := [2, 1, 5, 1, 2, 2, 2, 4]
def baseStart_21800 : Nat := 118140960795 + 21800 * 2 ^ 59
def prefixEnd_21800 : Nat := 4983230072969 + 3 ^ 40 * 21800 * 2
def baseEnd_21800 : Nat := 6633409344071076207259

theorem tailTrace_21800 : CollatzResearch.WordTrace tailWord_21800 prefixEnd_21800 6633409344071076207259 := by
  unfold tailWord_21800
  simp only [CollatzResearch.WordTrace]
  refine ⟨397555660514898994347427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 530074214019865325796569 397555660514898994347427)
  ·
    refine ⟨596333490772348491521141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 397555660514898994347427 596333490772348491521141)
    ·
      refine ⟨55906264759907671080107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 596333490772348491521141 55906264759907671080107)
      ·
        refine ⟨83859397139861506620161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55906264759907671080107 83859397139861506620161)
        ·
          refine ⟨62894547854896129965121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83859397139861506620161 62894547854896129965121)
          ·
            refine ⟨47170910891172097473841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62894547854896129965121 47170910891172097473841)
            ·
              refine ⟨35378183168379073105381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47170910891172097473841 35378183168379073105381)
              ·
                refine ⟨6633409344071076207259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35378183168379073105381 6633409344071076207259)
                ·
                  rfl

theorem cell19_21800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 4].length) (baseStart_21800 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_21800 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_21800 prefixEnd_21800 := by exact prefixLift 21800
  have htrace : WordTrace (prefixWord ++ tailWord_21800) baseStart_21800 baseEnd_21800 := by
    simpa [prefixWord, tailWord_21800, baseEnd_21800] using wordTrace_append hprefix tailTrace_21800
  have hstable : (prefixWord ++ tailWord_21800).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21800).length < 2 ^ (prefixWord ++ tailWord_21800).sum := by decide
  have hdescent : baseEnd_21800 < baseStart_21800 := by decide
  rcases family_descends (prefixWord ++ tailWord_21800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21859 : List Nat := [1, 1, 1, 5, 2, 2, 3, 4]
def baseStart_21859 : Nat := 118140960795 + 21859 * 2 ^ 59
def prefixEnd_21859 : Nat := 4983230072969 + 3 ^ 40 * 21859 * 2
def baseEnd_21859 : Nat := 6651362149176420895987

theorem tailTrace_21859 : CollatzResearch.WordTrace tailWord_21859 prefixEnd_21859 6651362149176420895987 := by
  unfold tailWord_21859
  simp only [CollatzResearch.WordTrace]
  refine ⟨797263227816051065092631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 531508818544034043395087 797263227816051065092631)
  ·
    refine ⟨1195894841724076597638947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 797263227816051065092631 1195894841724076597638947)
    ·
      refine ⟨1793842262586114896458421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1195894841724076597638947 1793842262586114896458421)
      ·
        refine ⟨168172712117448271542977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1793842262586114896458421 168172712117448271542977)
        ·
          refine ⟨126129534088086203657233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168172712117448271542977 126129534088086203657233)
          ·
            refine ⟨94597150566064652742925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126129534088086203657233 94597150566064652742925)
            ·
              refine ⟨35473931462274244778597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94597150566064652742925 35473931462274244778597)
              ·
                refine ⟨6651362149176420895987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35473931462274244778597 6651362149176420895987)
                ·
                  rfl

theorem cell19_21859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 4].length) (baseStart_21859 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_21859 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_21859 prefixEnd_21859 := by exact prefixLift 21859
  have htrace : WordTrace (prefixWord ++ tailWord_21859) baseStart_21859 baseEnd_21859 := by
    simpa [prefixWord, tailWord_21859, baseEnd_21859] using wordTrace_append hprefix tailTrace_21859
  have hstable : (prefixWord ++ tailWord_21859).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21859).length < 2 ^ (prefixWord ++ tailWord_21859).sum := by decide
  have hdescent : baseEnd_21859 < baseStart_21859 := by decide
  rcases family_descends (prefixWord ++ tailWord_21859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21897 : List Nat := [1, 2, 1, 1, 7, 1, 6]
def baseStart_21897 : Nat := 118140960795 + 21897 * 2 ^ 59
def prefixEnd_21897 : Nat := 4983230072969 + 3 ^ 40 * 21897 * 2
def baseEnd_21897 : Nat := 2220974990934530683813

theorem tailTrace_21897 : CollatzResearch.WordTrace tailWord_21897 prefixEnd_21897 2220974990934530683813 := by
  unfold tailWord_21897
  simp only [CollatzResearch.WordTrace]
  refine ⟨798649201678383554975945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 532432801118922369983963 798649201678383554975945)
  ·
    refine ⟨598986901258787666231959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 798649201678383554975945 598986901258787666231959)
    ·
      refine ⟨898480351888181499347939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 598986901258787666231959 898480351888181499347939)
      ·
        refine ⟨1347720527832272249021909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 898480351888181499347939 1347720527832272249021909)
        ·
          refine ⟨31587199871068880836451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 1347720527832272249021909 31587199871068880836451)
          ·
            refine ⟨47380799806603321254677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31587199871068880836451 47380799806603321254677)
            ·
              refine ⟨2220974990934530683813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 47380799806603321254677 2220974990934530683813)
              ·
                rfl

theorem cell19_21897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 6].length) (baseStart_21897 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_21897 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_21897 prefixEnd_21897 := by exact prefixLift 21897
  have htrace : WordTrace (prefixWord ++ tailWord_21897) baseStart_21897 baseEnd_21897 := by
    simpa [prefixWord, tailWord_21897, baseEnd_21897] using wordTrace_append hprefix tailTrace_21897
  have hstable : (prefixWord ++ tailWord_21897).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21897).length < 2 ^ (prefixWord ++ tailWord_21897).sum := by decide
  have hdescent : baseEnd_21897 < baseStart_21897 := by decide
  rcases family_descends (prefixWord ++ tailWord_21897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21899 : List Nat := [1, 1, 1, 1, 4, 3, 8]
def baseStart_21899 : Nat := 118140960795 + 21899 * 2 ^ 59
def prefixEnd_21899 : Nat := 4983230072969 + 3 ^ 40 * 21899 * 2
def baseEnd_21899 : Nat := 2221177847489393335663

theorem tailTrace_21899 : CollatzResearch.WordTrace tailWord_21899 prefixEnd_21899 2221177847489393335663 := by
  unfold tailWord_21899
  simp only [CollatzResearch.WordTrace]
  refine ⟨798722147671137896548751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 532481431780758597699167 798722147671137896548751)
  ·
    refine ⟨1198083221506706844823127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 798722147671137896548751 1198083221506706844823127)
    ·
      refine ⟨1797124832260060267234691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1198083221506706844823127 1797124832260060267234691)
      ·
        refine ⟨2695687248390090400852037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1797124832260060267234691 2695687248390090400852037)
        ·
          refine ⟨505441359073141950159757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2695687248390090400852037 505441359073141950159757)
          ·
            refine ⟨189540509652428231309909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 505441359073141950159757 189540509652428231309909)
            ·
              refine ⟨2221177847489393335663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 189540509652428231309909 2221177847489393335663)
              ·
                rfl

theorem cell19_21899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 8].length) (baseStart_21899 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_21899 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_21899 prefixEnd_21899 := by exact prefixLift 21899
  have htrace : WordTrace (prefixWord ++ tailWord_21899) baseStart_21899 baseEnd_21899 := by
    simpa [prefixWord, tailWord_21899, baseEnd_21899] using wordTrace_append hprefix tailTrace_21899
  have hstable : (prefixWord ++ tailWord_21899).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21899).length < 2 ^ (prefixWord ++ tailWord_21899).sum := by decide
  have hdescent : baseEnd_21899 < baseStart_21899 := by decide
  rcases family_descends (prefixWord ++ tailWord_21899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21933 : List Nat := [1, 5, 2, 2, 1, 2, 1, 5]
def baseStart_21933 : Nat := 118140960795 + 21933 * 2 ^ 59
def prefixEnd_21933 : Nat := 4983230072969 + 3 ^ 40 * 21933 * 2
def baseEnd_21933 : Nat := 6673879226766175251341

theorem tailTrace_21933 : CollatzResearch.WordTrace tailWord_21933 prefixEnd_21933 6673879226766175251341 := by
  unfold tailWord_21933
  simp only [CollatzResearch.WordTrace]
  refine ⟨799962229547961703286453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 533308153031974468857635 799962229547961703286453)
  ·
    refine ⟨74996459020121409683105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 799962229547961703286453 74996459020121409683105)
    ·
      refine ⟨56247344265091057262329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74996459020121409683105 56247344265091057262329)
      ·
        refine ⟨42185508198818292946747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56247344265091057262329 42185508198818292946747)
        ·
          refine ⟨63278262298227439420121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42185508198818292946747 63278262298227439420121)
          ·
            refine ⟨47458696723670579565091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63278262298227439420121 47458696723670579565091)
            ·
              refine ⟨71188045085505869347637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47458696723670579565091 71188045085505869347637)
              ·
                refine ⟨6673879226766175251341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71188045085505869347637 6673879226766175251341)
                ·
                  rfl

theorem cell19_21933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 5].length) (baseStart_21933 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_21933 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_21933 prefixEnd_21933 := by exact prefixLift 21933
  have htrace : WordTrace (prefixWord ++ tailWord_21933) baseStart_21933 baseEnd_21933 := by
    simpa [prefixWord, tailWord_21933, baseEnd_21933] using wordTrace_append hprefix tailTrace_21933
  have hstable : (prefixWord ++ tailWord_21933).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21933).length < 2 ^ (prefixWord ++ tailWord_21933).sum := by decide
  have hdescent : baseEnd_21933 < baseStart_21933 := by decide
  rcases family_descends (prefixWord ++ tailWord_21933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_21973 : List Nat := [1, 3, 2, 3, 1, 1, 4, 4]
def baseStart_21973 : Nat := 118140960795 + 21973 * 2 ^ 59
def prefixEnd_21973 : Nat := 4983230072969 + 3 ^ 40 * 21973 * 2
def baseEnd_21973 : Nat := 6686050620057934362343

theorem tailTrace_21973 : CollatzResearch.WordTrace tailWord_21973 prefixEnd_21973 6686050620057934362343 := by
  unfold tailWord_21973
  simp only [CollatzResearch.WordTrace]
  refine ⟨801421149403048534742573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 534280766268699023161715 801421149403048534742573)
  ·
    refine ⟨300532931026143200528465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 801421149403048534742573 300532931026143200528465)
    ·
      refine ⟨225399698269607400396349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 300532931026143200528465 225399698269607400396349)
      ·
        refine ⟨84524886851102775148631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 225399698269607400396349 84524886851102775148631)
        ·
          refine ⟨126787330276654162722947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84524886851102775148631 126787330276654162722947)
          ·
            refine ⟨190180995414981244084421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126787330276654162722947 190180995414981244084421)
            ·
              refine ⟨35658936640308983265829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 190180995414981244084421 35658936640308983265829)
              ·
                refine ⟨6686050620057934362343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35658936640308983265829 6686050620057934362343)
                ·
                  rfl

theorem cell19_21973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 4].length) (baseStart_21973 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_21973 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_21973 prefixEnd_21973 := by exact prefixLift 21973
  have htrace : WordTrace (prefixWord ++ tailWord_21973) baseStart_21973 baseEnd_21973 := by
    simpa [prefixWord, tailWord_21973, baseEnd_21973] using wordTrace_append hprefix tailTrace_21973
  have hstable : (prefixWord ++ tailWord_21973).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_21973).length < 2 ^ (prefixWord ++ tailWord_21973).sum := by decide
  have hdescent : baseEnd_21973 < baseStart_21973 := by decide
  rcases family_descends (prefixWord ++ tailWord_21973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22013 : List Nat := [1, 4, 1, 1, 1, 11]
def baseStart_22013 : Nat := 118140960795 + 22013 * 2 ^ 59
def prefixEnd_22013 : Nat := 4983230072969 + 3 ^ 40 * 22013 * 2
def baseEnd_22013 : Nat := 744246890372188163705

theorem tailTrace_22013 : CollatzResearch.WordTrace tailWord_22013 prefixEnd_22013 744246890372188163705 := by
  unfold tailWord_22013
  simp only [CollatzResearch.WordTrace]
  refine ⟨802880069258135366198693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 535253379505423577465795 802880069258135366198693)
  ·
    refine ⟨150540012985900381162255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 802880069258135366198693 150540012985900381162255)
    ·
      refine ⟨225810019478850571743383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150540012985900381162255 225810019478850571743383)
      ·
        refine ⟨338715029218275857615075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225810019478850571743383 338715029218275857615075)
        ·
          refine ⟨508072543827413786422613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338715029218275857615075 508072543827413786422613)
          ·
            refine ⟨744246890372188163705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 508072543827413786422613 744246890372188163705)
            ·
              rfl

theorem cell19_22013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 11].length) (baseStart_22013 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_22013 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_22013 prefixEnd_22013 := by exact prefixLift 22013
  have htrace : WordTrace (prefixWord ++ tailWord_22013) baseStart_22013 baseEnd_22013 := by
    simpa [prefixWord, tailWord_22013, baseEnd_22013] using wordTrace_append hprefix tailTrace_22013
  have hstable : (prefixWord ++ tailWord_22013).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22013).length < 2 ^ (prefixWord ++ tailWord_22013).sum := by decide
  have hdescent : baseEnd_22013 < baseStart_22013 := by decide
  rcases family_descends (prefixWord ++ tailWord_22013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22022 : List Nat := [6, 2, 1, 1, 2, 2, 1, 4]
def baseStart_22022 : Nat := 118140960795 + 22022 * 2 ^ 59
def prefixEnd_22022 : Nat := 4983230072969 + 3 ^ 40 * 22022 * 2
def baseEnd_22022 : Nat := 6700960576840339273321

theorem tailTrace_22022 : CollatzResearch.WordTrace tailWord_22022 prefixEnd_22022 6700960576840339273321 := by
  unfold tailWord_22022
  simp only [CollatzResearch.WordTrace]
  refine ⟨25100260194547809477385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 535472217483686602184213 25100260194547809477385)
  ·
    refine ⟨18825195145910857108039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25100260194547809477385 18825195145910857108039)
    ·
      refine ⟨28237792718866285662059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18825195145910857108039 28237792718866285662059)
      ·
        refine ⟨42356689078299428493089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28237792718866285662059 42356689078299428493089)
        ·
          refine ⟨31767516808724571369817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42356689078299428493089 31767516808724571369817)
          ·
            refine ⟨23825637606543428527363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31767516808724571369817 23825637606543428527363)
            ·
              refine ⟨35738456409815142791045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23825637606543428527363 35738456409815142791045)
              ·
                refine ⟨6700960576840339273321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35738456409815142791045 6700960576840339273321)
                ·
                  rfl

theorem cell19_22022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_22022 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_22022 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_22022 prefixEnd_22022 := by exact prefixLift 22022
  have htrace : WordTrace (prefixWord ++ tailWord_22022) baseStart_22022 baseEnd_22022 := by
    simpa [prefixWord, tailWord_22022, baseEnd_22022] using wordTrace_append hprefix tailTrace_22022
  have hstable : (prefixWord ++ tailWord_22022).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22022).length < 2 ^ (prefixWord ++ tailWord_22022).sum := by decide
  have hdescent : baseEnd_22022 < baseStart_22022 := by decide
  rcases family_descends (prefixWord ++ tailWord_22022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22028 : List Nat := [2, 2, 1, 2, 5, 2, 1, 4]
def baseStart_22028 : Nat := 118140960795 + 22028 * 2 ^ 59
def prefixEnd_22028 : Nat := 4983230072969 + 3 ^ 40 * 22028 * 2
def baseEnd_22028 : Nat := 6702786285834103139971

theorem tailTrace_22028 : CollatzResearch.WordTrace tailWord_22028 prefixEnd_22028 6702786285834103139971 := by
  unfold tailWord_22028
  simp only [CollatzResearch.WordTrace]
  refine ⟨401713582101896463997369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 535618109469195285329825 401713582101896463997369)
  ·
    refine ⟨301285186576422347998027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 401713582101896463997369 301285186576422347998027)
    ·
      refine ⟨451927779864633521997041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301285186576422347998027 451927779864633521997041)
      ·
        refine ⟨338945834898475141497781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 451927779864633521997041 338945834898475141497781)
        ·
          refine ⟨31776172021732044515417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 338945834898475141497781 31776172021732044515417)
          ·
            refine ⟨23832129016299033386563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31776172021732044515417 23832129016299033386563)
            ·
              refine ⟨35748193524448550079845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23832129016299033386563 35748193524448550079845)
              ·
                refine ⟨6702786285834103139971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35748193524448550079845 6702786285834103139971)
                ·
                  rfl

theorem cell19_22028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 4].length) (baseStart_22028 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_22028 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_22028 prefixEnd_22028 := by exact prefixLift 22028
  have htrace : WordTrace (prefixWord ++ tailWord_22028) baseStart_22028 baseEnd_22028 := by
    simpa [prefixWord, tailWord_22028, baseEnd_22028] using wordTrace_append hprefix tailTrace_22028
  have hstable : (prefixWord ++ tailWord_22028).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22028).length < 2 ^ (prefixWord ++ tailWord_22028).sum := by decide
  have hdescent : baseEnd_22028 < baseStart_22028 := by decide
  rcases family_descends (prefixWord ++ tailWord_22028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22197 : List Nat := [1, 3, 3, 3, 3, 1, 1, 4]
def baseStart_22197 : Nat := 118140960795 + 22197 * 2 ^ 59
def prefixEnd_22197 : Nat := 4983230072969 + 3 ^ 40 * 22197 * 2
def baseEnd_22197 : Nat := 6754210422491785383955

theorem tailTrace_22197 : CollatzResearch.WordTrace tailWord_22197 prefixEnd_22197 6754210422491785383955 := by
  unfold tailWord_22197
  simp only [CollatzResearch.WordTrace]
  refine ⟨809591100591534790896845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 539727400394356527264563 809591100591534790896845)
  ·
    refine ⟨303596662721825546586317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 809591100591534790896845 303596662721825546586317)
    ·
      refine ⟨113848748520684579969869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 303596662721825546586317 113848748520684579969869)
      ·
        refine ⟨42693280695256717488701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113848748520684579969869 42693280695256717488701)
        ·
          refine ⟨16009980260721269058263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42693280695256717488701 16009980260721269058263)
          ·
            refine ⟨24014970391081903587395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16009980260721269058263 24014970391081903587395)
            ·
              refine ⟨36022455586622855381093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24014970391081903587395 36022455586622855381093)
              ·
                refine ⟨6754210422491785383955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36022455586622855381093 6754210422491785383955)
                ·
                  rfl

theorem cell19_22197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 4].length) (baseStart_22197 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_22197 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_22197 prefixEnd_22197 := by exact prefixLift 22197
  have htrace : WordTrace (prefixWord ++ tailWord_22197) baseStart_22197 baseEnd_22197 := by
    simpa [prefixWord, tailWord_22197, baseEnd_22197] using wordTrace_append hprefix tailTrace_22197
  have hstable : (prefixWord ++ tailWord_22197).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22197).length < 2 ^ (prefixWord ++ tailWord_22197).sum := by decide
  have hdescent : baseEnd_22197 < baseStart_22197 := by decide
  rcases family_descends (prefixWord ++ tailWord_22197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22214 : List Nat := [6, 1, 2, 1, 1, 2, 3, 3]
def baseStart_22214 : Nat := 118140960795 + 22214 * 2 ^ 59
def prefixEnd_22214 : Nat := 4983230072969 + 3 ^ 40 * 22214 * 2
def baseEnd_22214 : Nat := 6759383264640783006131

theorem tailTrace_22214 : CollatzResearch.WordTrace tailWord_22214 prefixEnd_22214 6759383264640783006131 := by
  unfold tailWord_22214
  simp only [CollatzResearch.WordTrace]
  refine ⟨25319098172810834195803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 540140761019964462843797 25319098172810834195803)
  ·
    refine ⟨37978647259216251293705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25319098172810834195803 37978647259216251293705)
    ·
      refine ⟨28483985444412188470279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37978647259216251293705 28483985444412188470279)
      ·
        refine ⟨42725978166618282705419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28483985444412188470279 42725978166618282705419)
        ·
          refine ⟨64088967249927424058129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42725978166618282705419 64088967249927424058129)
          ·
            refine ⟨48066725437445568043597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64088967249927424058129 48066725437445568043597)
            ·
              refine ⟨18025022039042088016349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48066725437445568043597 18025022039042088016349)
              ·
                refine ⟨6759383264640783006131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18025022039042088016349 6759383264640783006131)
                ·
                  rfl

theorem cell19_22214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_22214 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_22214 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_22214 prefixEnd_22214 := by exact prefixLift 22214
  have htrace : WordTrace (prefixWord ++ tailWord_22214) baseStart_22214 baseEnd_22214 := by
    simpa [prefixWord, tailWord_22214, baseEnd_22214] using wordTrace_append hprefix tailTrace_22214
  have hstable : (prefixWord ++ tailWord_22214).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22214).length < 2 ^ (prefixWord ++ tailWord_22214).sum := by decide
  have hdescent : baseEnd_22214 < baseStart_22214 := by decide
  rcases family_descends (prefixWord ++ tailWord_22214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22218 : List Nat := [3, 1, 2, 1, 5, 1, 3, 3]
def baseStart_22218 : Nat := 118140960795 + 22218 * 2 ^ 59
def prefixEnd_22218 : Nat := 4983230072969 + 3 ^ 40 * 22218 * 2
def baseEnd_22218 : Nat := 6760600403969958917231

theorem tailTrace_22218 : CollatzResearch.WordTrace tailWord_22218 prefixEnd_22218 6760600403969958917231 := by
  unfold tailWord_22218
  simp only [CollatzResearch.WordTrace]
  refine ⟨202589258378863844352827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 540238022343636918274205 202589258378863844352827)
  ·
    refine ⟨303883887568295766529241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202589258378863844352827 303883887568295766529241)
    ·
      refine ⟨227912915676221824896931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 303883887568295766529241 227912915676221824896931)
      ·
        refine ⟨341869373514332737345397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227912915676221824896931 341869373514332737345397)
        ·
          refine ⟨32050253766968694126131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 341869373514332737345397 32050253766968694126131)
          ·
            refine ⟨48075380650453041189197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32050253766968694126131 48075380650453041189197)
            ·
              refine ⟨18028267743919890445949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48075380650453041189197 18028267743919890445949)
              ·
                refine ⟨6760600403969958917231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18028267743919890445949 6760600403969958917231)
                ·
                  rfl

theorem cell19_22218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 3].length) (baseStart_22218 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_22218 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_22218 prefixEnd_22218 := by exact prefixLift 22218
  have htrace : WordTrace (prefixWord ++ tailWord_22218) baseStart_22218 baseEnd_22218 := by
    simpa [prefixWord, tailWord_22218, baseEnd_22218] using wordTrace_append hprefix tailTrace_22218
  have hstable : (prefixWord ++ tailWord_22218).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22218).length < 2 ^ (prefixWord ++ tailWord_22218).sum := by decide
  have hdescent : baseEnd_22218 < baseStart_22218 := by decide
  rcases family_descends (prefixWord ++ tailWord_22218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22237 : List Nat := [1, 4, 3, 3, 1, 1, 6]
def baseStart_22237 : Nat := 118140960795 + 22237 * 2 ^ 59
def prefixEnd_22237 : Nat := 4983230072969 + 3 ^ 40 * 22237 * 2
def baseEnd_22237 : Nat := 2255460605261181498319

theorem tailTrace_22237 : CollatzResearch.WordTrace tailWord_22237 prefixEnd_22237 2255460605261181498319 := by
  unfold tailWord_22237
  simp only [CollatzResearch.WordTrace]
  refine ⟨811050020446621622352965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 540700013631081081568643 811050020446621622352965)
  ·
    refine ⟨152071878833741554191181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 811050020446621622352965 152071878833741554191181)
    ·
      refine ⟨57026954562653082821693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152071878833741554191181 57026954562653082821693)
      ·
        refine ⟨21385107960994906058135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57026954562653082821693 21385107960994906058135)
        ·
          refine ⟨32077661941492359087203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21385107960994906058135 32077661941492359087203)
          ·
            refine ⟨48116492912238538630805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32077661941492359087203 48116492912238538630805)
            ·
              refine ⟨2255460605261181498319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48116492912238538630805 2255460605261181498319)
              ·
                rfl

theorem cell19_22237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 6].length) (baseStart_22237 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_22237 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_22237 prefixEnd_22237 := by exact prefixLift 22237
  have htrace : WordTrace (prefixWord ++ tailWord_22237) baseStart_22237 baseEnd_22237 := by
    simpa [prefixWord, tailWord_22237, baseEnd_22237] using wordTrace_append hprefix tailTrace_22237
  have hstable : (prefixWord ++ tailWord_22237).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22237).length < 2 ^ (prefixWord ++ tailWord_22237).sum := by decide
  have hdescent : baseEnd_22237 < baseStart_22237 := by decide
  rcases family_descends (prefixWord ++ tailWord_22237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22298 : List Nat := [3, 1, 1, 3, 2, 2, 7]
def baseStart_22298 : Nat := 118140960795 + 22298 * 2 ^ 59
def prefixEnd_22298 : Nat := 4983230072969 + 3 ^ 40 * 22298 * 2
def baseEnd_22298 : Nat := 2261647730184492379745

theorem tailTrace_22298 : CollatzResearch.WordTrace tailWord_22298 prefixEnd_22298 2261647730184492379745 := by
  unfold tailWord_22298
  simp only [CollatzResearch.WordTrace]
  refine ⟨203318718306407260080887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 542183248817086026882365 203318718306407260080887)
  ·
    refine ⟨304978077459610890121331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203318718306407260080887 304978077459610890121331)
    ·
      refine ⟨457467116189416335181997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304978077459610890121331 457467116189416335181997)
      ·
        refine ⟨171550168571031125693249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 457467116189416335181997 171550168571031125693249)
        ·
          refine ⟨128662626428273344269937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171550168571031125693249 128662626428273344269937)
          ·
            refine ⟨96496969821205008202453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128662626428273344269937 96496969821205008202453)
            ·
              refine ⟨2261647730184492379745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 96496969821205008202453 2261647730184492379745)
              ·
                rfl

theorem cell19_22298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 7].length) (baseStart_22298 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_22298 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_22298 prefixEnd_22298 := by exact prefixLift 22298
  have htrace : WordTrace (prefixWord ++ tailWord_22298) baseStart_22298 baseEnd_22298 := by
    simpa [prefixWord, tailWord_22298, baseEnd_22298] using wordTrace_append hprefix tailTrace_22298
  have hstable : (prefixWord ++ tailWord_22298).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22298).length < 2 ^ (prefixWord ++ tailWord_22298).sum := by decide
  have hdescent : baseEnd_22298 < baseStart_22298 := by decide
  rcases family_descends (prefixWord ++ tailWord_22298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22334 : List Nat := [4, 2, 1, 2, 2, 1, 2, 5]
def baseStart_22334 : Nat := 118140960795 + 22334 * 2 ^ 59
def prefixEnd_22334 : Nat := 4983230072969 + 3 ^ 40 * 22334 * 2
def baseEnd_22334 : Nat := 6795897444516060339137

theorem tailTrace_22334 : CollatzResearch.WordTrace tailWord_22334 prefixEnd_22334 6795897444516060339137 := by
  unfold tailWord_22334
  simp only [CollatzResearch.WordTrace]
  refine ⟨101823487636900898579257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 543058600730138125756037 101823487636900898579257)
  ·
    refine ⟨76367615727675673934443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101823487636900898579257 76367615727675673934443)
    ·
      refine ⟨114551423591513510901665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76367615727675673934443 114551423591513510901665)
      ·
        refine ⟨85913567693635133176249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114551423591513510901665 85913567693635133176249)
        ·
          refine ⟨64435175770226349882187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85913567693635133176249 64435175770226349882187)
          ·
            refine ⟨96652763655339524823281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64435175770226349882187 96652763655339524823281)
            ·
              refine ⟨72489572741504643617461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96652763655339524823281 72489572741504643617461)
              ·
                refine ⟨6795897444516060339137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72489572741504643617461 6795897444516060339137)
                ·
                  rfl

theorem cell19_22334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_22334 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_22334 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_22334 prefixEnd_22334 := by exact prefixLift 22334
  have htrace : WordTrace (prefixWord ++ tailWord_22334) baseStart_22334 baseEnd_22334 := by
    simpa [prefixWord, tailWord_22334, baseEnd_22334] using wordTrace_append hprefix tailTrace_22334
  have hstable : (prefixWord ++ tailWord_22334).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22334).length < 2 ^ (prefixWord ++ tailWord_22334).sum := by decide
  have hdescent : baseEnd_22334 < baseStart_22334 := by decide
  rcases family_descends (prefixWord ++ tailWord_22334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22370 : List Nat := [3, 3, 2, 1, 2, 3, 1, 4]
def baseStart_22370 : Nat := 118140960795 + 22370 * 2 ^ 59
def prefixEnd_22370 : Nat := 4983230072969 + 3 ^ 40 * 22370 * 2
def baseEnd_22370 : Nat := 6806851698478643539039

theorem tailTrace_22370 : CollatzResearch.WordTrace tailWord_22370 prefixEnd_22370 6806851698478643539039 := by
  unfold tailWord_22370
  simp only [CollatzResearch.WordTrace]
  refine ⟨203975232241196334236141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 543933952643190224629709 203975232241196334236141)
  ·
    refine ⟨76490712090448625338553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203975232241196334236141 76490712090448625338553)
    ·
      refine ⟨57368034067836469003915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76490712090448625338553 57368034067836469003915)
      ·
        refine ⟨86052051101754703505873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57368034067836469003915 86052051101754703505873)
        ·
          refine ⟨64539038326316027629405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86052051101754703505873 64539038326316027629405)
          ·
            refine ⟨24202139372368510361027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64539038326316027629405 24202139372368510361027)
            ·
              refine ⟨36303209058552765541541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24202139372368510361027 36303209058552765541541)
              ·
                refine ⟨6806851698478643539039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36303209058552765541541 6806851698478643539039)
                ·
                  rfl

theorem cell19_22370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 4].length) (baseStart_22370 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_22370 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_22370 prefixEnd_22370 := by exact prefixLift 22370
  have htrace : WordTrace (prefixWord ++ tailWord_22370) baseStart_22370 baseEnd_22370 := by
    simpa [prefixWord, tailWord_22370, baseEnd_22370] using wordTrace_append hprefix tailTrace_22370
  have hstable : (prefixWord ++ tailWord_22370).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22370).length < 2 ^ (prefixWord ++ tailWord_22370).sum := by decide
  have hdescent : baseEnd_22370 < baseStart_22370 := by decide
  rcases family_descends (prefixWord ++ tailWord_22370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22410 : List Nat := [3, 1, 2, 4, 2, 1, 6]
def baseStart_22410 : Nat := 118140960795 + 22410 * 2 ^ 59
def prefixEnd_22410 : Nat := 4983230072969 + 3 ^ 40 * 22410 * 2
def baseEnd_22410 : Nat := 2273007697256800883347

theorem tailTrace_22410 : CollatzResearch.WordTrace tailWord_22410 prefixEnd_22410 2273007697256800883347 := by
  unfold tailWord_22410
  simp only [CollatzResearch.WordTrace]
  refine ⟨204339962204968042100171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 544906565879914778933789 204339962204968042100171)
  ·
    refine ⟨306509943307452063150257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204339962204968042100171 306509943307452063150257)
    ·
      refine ⟨229882457480589047362693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 306509943307452063150257 229882457480589047362693)
      ·
        refine ⟨43102960777610446380505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 229882457480589047362693 43102960777610446380505)
        ·
          refine ⟨32327220583207834785379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43102960777610446380505 32327220583207834785379)
          ·
            refine ⟨48490830874811752178069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32327220583207834785379 48490830874811752178069)
            ·
              refine ⟨2273007697256800883347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48490830874811752178069 2273007697256800883347)
              ·
                rfl

theorem cell19_22410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 6].length) (baseStart_22410 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_22410 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_22410 prefixEnd_22410 := by exact prefixLift 22410
  have htrace : WordTrace (prefixWord ++ tailWord_22410) baseStart_22410 baseEnd_22410 := by
    simpa [prefixWord, tailWord_22410, baseEnd_22410] using wordTrace_append hprefix tailTrace_22410
  have hstable : (prefixWord ++ tailWord_22410).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22410).length < 2 ^ (prefixWord ++ tailWord_22410).sum := by decide
  have hdescent : baseEnd_22410 < baseStart_22410 := by decide
  rcases family_descends (prefixWord ++ tailWord_22410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22488 : List Nat := [2, 1, 2, 2, 2, 2, 4, 4]
def baseStart_22488 : Nat := 118140960795 + 22488 * 2 ^ 59
def prefixEnd_22488 : Nat := 4983230072969 + 3 ^ 40 * 22488 * 2
def baseEnd_22488 : Nat := 6842757308689332916495

theorem tailTrace_22488 : CollatzResearch.WordTrace tailWord_22488 prefixEnd_22488 6842757308689332916495 := by
  unfold tailWord_22488
  simp only [CollatzResearch.WordTrace]
  refine ⟨410102371268645744870059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 546803161691527659826745 410102371268645744870059)
  ·
    refine ⟨615153556902968617305089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 410102371268645744870059 615153556902968617305089)
    ·
      refine ⟨461365167677226462978817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 615153556902968617305089 461365167677226462978817)
      ·
        refine ⟨346023875757919847234113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 461365167677226462978817 346023875757919847234113)
        ·
          refine ⟨259517906818439885425585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 346023875757919847234113 259517906818439885425585)
          ·
            refine ⟨194638430113829914069189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 259517906818439885425585 194638430113829914069189)
            ·
              refine ⟨36494705646343108887973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 194638430113829914069189 36494705646343108887973)
              ·
                refine ⟨6842757308689332916495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36494705646343108887973 6842757308689332916495)
                ·
                  rfl

theorem cell19_22488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 4].length) (baseStart_22488 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_22488 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_22488 prefixEnd_22488 := by exact prefixLift 22488
  have htrace : WordTrace (prefixWord ++ tailWord_22488) baseStart_22488 baseEnd_22488 := by
    simpa [prefixWord, tailWord_22488, baseEnd_22488] using wordTrace_append hprefix tailTrace_22488
  have hstable : (prefixWord ++ tailWord_22488).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22488).length < 2 ^ (prefixWord ++ tailWord_22488).sum := by decide
  have hdescent : baseEnd_22488 < baseStart_22488 := by decide
  rcases family_descends (prefixWord ++ tailWord_22488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22562 : List Nat := [3, 3, 1, 1, 1, 2, 5, 3]
def baseStart_22562 : Nat := 118140960795 + 22562 * 2 ^ 59
def prefixEnd_22562 : Nat := 4983230072969 + 3 ^ 40 * 22562 * 2
def baseEnd_22562 : Nat := 6865274386279087271849

theorem tailTrace_22562 : CollatzResearch.WordTrace tailWord_22562 prefixEnd_22562 6865274386279087271849 := by
  unfold tailWord_22562
  simp only [CollatzResearch.WordTrace]
  refine ⟨205725936067300531983485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 548602496179468085289293 205725936067300531983485)
  ·
    refine ⟨77147226025237699493807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205725936067300531983485 77147226025237699493807)
    ·
      refine ⟨115720839037856549240711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77147226025237699493807 115720839037856549240711)
      ·
        refine ⟨173581258556784823861067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115720839037856549240711 173581258556784823861067)
        ·
          refine ⟨260371887835177235791601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173581258556784823861067 260371887835177235791601)
          ·
            refine ⟨195278915876382926843701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 260371887835177235791601 195278915876382926843701)
            ·
              refine ⟨18307398363410899391597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 195278915876382926843701 18307398363410899391597)
              ·
                refine ⟨6865274386279087271849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18307398363410899391597 6865274386279087271849)
                ·
                  rfl

theorem cell19_22562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 3].length) (baseStart_22562 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_22562 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_22562 prefixEnd_22562 := by exact prefixLift 22562
  have htrace : WordTrace (prefixWord ++ tailWord_22562) baseStart_22562 baseEnd_22562 := by
    simpa [prefixWord, tailWord_22562, baseEnd_22562] using wordTrace_append hprefix tailTrace_22562
  have hstable : (prefixWord ++ tailWord_22562).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22562).length < 2 ^ (prefixWord ++ tailWord_22562).sum := by decide
  have hdescent : baseEnd_22562 < baseStart_22562 := by decide
  rcases family_descends (prefixWord ++ tailWord_22562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22640 : List Nat := [2, 1, 1, 1, 5, 4, 5]
def baseStart_22640 : Nat := 118140960795 + 22640 * 2 ^ 59
def prefixEnd_22640 : Nat := 4983230072969 + 3 ^ 40 * 22640 * 2
def baseEnd_22640 : Nat := 2296336201066005846101

theorem tailTrace_22640 : CollatzResearch.WordTrace tailWord_22640 prefixEnd_22640 2296336201066005846101 := by
  unfold tailWord_22640
  simp only [CollatzResearch.WordTrace]
  refine ⟨412874318993310724636687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 550499091991080966182249 412874318993310724636687)
  ·
    refine ⟨619311478489966086955031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 412874318993310724636687 619311478489966086955031)
    ·
      refine ⟨928967217734949130432547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 619311478489966086955031 928967217734949130432547)
      ·
        refine ⟨1393450826602423695648821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 928967217734949130432547 1393450826602423695648821)
        ·
          refine ⟨130636014993977221467077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1393450826602423695648821 130636014993977221467077)
          ·
            refine ⟨24494252811370729025077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130636014993977221467077 24494252811370729025077)
            ·
              refine ⟨2296336201066005846101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24494252811370729025077 2296336201066005846101)
              ·
                rfl

theorem cell19_22640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 5].length) (baseStart_22640 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_22640 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_22640 prefixEnd_22640 := by exact prefixLift 22640
  have htrace : WordTrace (prefixWord ++ tailWord_22640) baseStart_22640 baseEnd_22640 := by
    simpa [prefixWord, tailWord_22640, baseEnd_22640] using wordTrace_append hprefix tailTrace_22640
  have hstable : (prefixWord ++ tailWord_22640).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22640).length < 2 ^ (prefixWord ++ tailWord_22640).sum := by decide
  have hdescent : baseEnd_22640 < baseStart_22640 := by decide
  rcases family_descends (prefixWord ++ tailWord_22640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22657 : List Nat := [1, 2, 4, 2, 3, 1, 2, 4]
def baseStart_22657 : Nat := 118140960795 + 22657 * 2 ^ 59
def prefixEnd_22657 : Nat := 4983230072969 + 3 ^ 40 * 22657 * 2
def baseEnd_22657 : Nat := 6894181445347015160479

theorem tailTrace_22657 : CollatzResearch.WordTrace tailWord_22657 prefixEnd_22657 6894181445347015160479 := by
  unfold tailWord_22657
  simp only [CollatzResearch.WordTrace]
  refine ⟨826368678925033352642225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 550912452616688901761483 826368678925033352642225)
  ·
    refine ⟨619776509193775014481669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 826368678925033352642225 619776509193775014481669)
    ·
      refine ⟨116208095473832815215313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 619776509193775014481669 116208095473832815215313)
      ·
        refine ⟨87156071605374611411485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116208095473832815215313 87156071605374611411485)
        ·
          refine ⟨32683526852015479279307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87156071605374611411485 32683526852015479279307)
          ·
            refine ⟨49025290278023218918961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32683526852015479279307 49025290278023218918961)
            ·
              refine ⟨36768967708517414189221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49025290278023218918961 36768967708517414189221)
              ·
                refine ⟨6894181445347015160479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36768967708517414189221 6894181445347015160479)
                ·
                  rfl

theorem cell19_22657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 4].length) (baseStart_22657 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_22657 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_22657 prefixEnd_22657 := by exact prefixLift 22657
  have htrace : WordTrace (prefixWord ++ tailWord_22657) baseStart_22657 baseEnd_22657 := by
    simpa [prefixWord, tailWord_22657, baseEnd_22657] using wordTrace_append hprefix tailTrace_22657
  have hstable : (prefixWord ++ tailWord_22657).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22657).length < 2 ^ (prefixWord ++ tailWord_22657).sum := by decide
  have hdescent : baseEnd_22657 < baseStart_22657 := by decide
  rcases family_descends (prefixWord ++ tailWord_22657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22659 : List Nat := [1, 1, 1, 3, 3, 4, 2, 4]
def baseStart_22659 : Nat := 118140960795 + 22659 * 2 ^ 59
def prefixEnd_22659 : Nat := 4983230072969 + 3 ^ 40 * 22659 * 2
def baseEnd_22659 : Nat := 6894790015011603116029

theorem tailTrace_22659 : CollatzResearch.WordTrace tailWord_22659 prefixEnd_22659 6894790015011603116029 := by
  unfold tailWord_22659
  simp only [CollatzResearch.WordTrace]
  refine ⟨826441624917787694215031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 550961083278525129476687 826441624917787694215031)
  ·
    refine ⟨1239662437376681541322547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 826441624917787694215031 1239662437376681541322547)
    ·
      refine ⟨1859493656065022311983821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1239662437376681541322547 1859493656065022311983821)
      ·
        refine ⟨697310121024383366993933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1859493656065022311983821 697310121024383366993933)
        ·
          refine ⟨261491295384143762622725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 697310121024383366993933 261491295384143762622725)
          ·
            refine ⟨49029617884526955491761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 261491295384143762622725 49029617884526955491761)
            ·
              refine ⟨36772213413395216618821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49029617884526955491761 36772213413395216618821)
              ·
                refine ⟨6894790015011603116029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36772213413395216618821 6894790015011603116029)
                ·
                  rfl

theorem cell19_22659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 4].length) (baseStart_22659 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_22659 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_22659 prefixEnd_22659 := by exact prefixLift 22659
  have htrace : WordTrace (prefixWord ++ tailWord_22659) baseStart_22659 baseEnd_22659 := by
    simpa [prefixWord, tailWord_22659, baseEnd_22659] using wordTrace_append hprefix tailTrace_22659
  have hstable : (prefixWord ++ tailWord_22659).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22659).length < 2 ^ (prefixWord ++ tailWord_22659).sum := by decide
  have hdescent : baseEnd_22659 < baseStart_22659 := by decide
  rcases family_descends (prefixWord ++ tailWord_22659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22695 : List Nat := [1, 1, 6, 2, 3, 6]
def baseStart_22695 : Nat := 118140960795 + 22695 * 2 ^ 59
def prefixEnd_22695 : Nat := 4983230072969 + 3 ^ 40 * 22695 * 2
def baseEnd_22695 : Nat := 767304918774909590659

theorem tailTrace_22695 : CollatzResearch.WordTrace tailWord_22695 prefixEnd_22695 767304918774909590659 := by
  unfold tailWord_22695
  simp only [CollatzResearch.WordTrace]
  refine ⟨827754652787365842525539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 551836435191577228350359 827754652787365842525539)
  ·
    refine ⟨1241631979181048763788309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 827754652787365842525539 1241631979181048763788309)
    ·
      refine ⟨58201499024111660802577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1241631979181048763788309 58201499024111660802577)
      ·
        refine ⟨43651124268083745601933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58201499024111660802577 43651124268083745601933)
        ·
          refine ⟨16369171600531404600725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43651124268083745601933 16369171600531404600725)
          ·
            refine ⟨767304918774909590659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16369171600531404600725 767304918774909590659)
            ·
              rfl

theorem cell19_22695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 6].length) (baseStart_22695 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_22695 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_22695 prefixEnd_22695 := by exact prefixLift 22695
  have htrace : WordTrace (prefixWord ++ tailWord_22695) baseStart_22695 baseEnd_22695 := by
    simpa [prefixWord, tailWord_22695, baseEnd_22695] using wordTrace_append hprefix tailTrace_22695
  have hstable : (prefixWord ++ tailWord_22695).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22695).length < 2 ^ (prefixWord ++ tailWord_22695).sum := by decide
  have hdescent : baseEnd_22695 < baseStart_22695 := by decide
  rcases family_descends (prefixWord ++ tailWord_22695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22708 : List Nat := [2, 5, 3, 1, 1, 2, 1, 4]
def baseStart_22708 : Nat := 118140960795 + 22708 * 2 ^ 59
def prefixEnd_22708 : Nat := 4983230072969 + 3 ^ 40 * 22708 * 2
def baseEnd_22708 : Nat := 6909699971794008027007

theorem tailTrace_22708 : CollatzResearch.WordTrace tailWord_22708 prefixEnd_22708 6909699971794008027007 := by
  unfold tailWord_22708
  simp only [CollatzResearch.WordTrace]
  refine ⟨414114400870134531374389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 552152534493512708499185 414114400870134531374389)
  ·
    refine ⟨38823225081575112316349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 414114400870134531374389 38823225081575112316349)
    ·
      refine ⟨14558709405590667118631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38823225081575112316349 14558709405590667118631)
      ·
        refine ⟨21838064108386000677947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14558709405590667118631 21838064108386000677947)
        ·
          refine ⟨32757096162579001016921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21838064108386000677947 32757096162579001016921)
          ·
            refine ⟨24567822121934250762691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32757096162579001016921 24567822121934250762691)
            ·
              refine ⟨36851733182901376144037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24567822121934250762691 36851733182901376144037)
              ·
                refine ⟨6909699971794008027007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36851733182901376144037 6909699971794008027007)
                ·
                  rfl

theorem cell19_22708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 4].length) (baseStart_22708 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_22708 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_22708 prefixEnd_22708 := by exact prefixLift 22708
  have htrace : WordTrace (prefixWord ++ tailWord_22708) baseStart_22708 baseEnd_22708 := by
    simpa [prefixWord, tailWord_22708, baseEnd_22708] using wordTrace_append hprefix tailTrace_22708
  have hstable : (prefixWord ++ tailWord_22708).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22708).length < 2 ^ (prefixWord ++ tailWord_22708).sum := by decide
  have hdescent : baseEnd_22708 < baseStart_22708 := by decide
  rcases family_descends (prefixWord ++ tailWord_22708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22735 : List Nat := [1, 1, 2, 1, 1, 3, 7, 3]
def baseStart_22735 : Nat := 118140960795 + 22735 * 2 ^ 59
def prefixEnd_22735 : Nat := 4983230072969 + 3 ^ 40 * 22735 * 2
def baseEnd_22735 : Nat := 6917915662265945426933

theorem tailTrace_22735 : CollatzResearch.WordTrace tailWord_22735 prefixEnd_22735 6917915662265945426933 := by
  unfold tailWord_22735
  simp only [CollatzResearch.WordTrace]
  refine ⟨829213572642452673981659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 552809048428301782654439 829213572642452673981659)
  ·
    refine ⟨1243820358963679010972489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 829213572642452673981659 1243820358963679010972489)
    ·
      refine ⟨932865269222759258229367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1243820358963679010972489 932865269222759258229367)
      ·
        refine ⟨1399297903834138887344051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 932865269222759258229367 1399297903834138887344051)
        ·
          refine ⟨2098946855751208331016077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1399297903834138887344051 2098946855751208331016077)
          ·
            refine ⟨787105070906703124131029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2098946855751208331016077 787105070906703124131029)
            ·
              refine ⟨18447775099375854471821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 787105070906703124131029 18447775099375854471821)
              ·
                refine ⟨6917915662265945426933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18447775099375854471821 6917915662265945426933)
                ·
                  rfl

theorem cell19_22735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 3].length) (baseStart_22735 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_22735 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_22735 prefixEnd_22735 := by exact prefixLift 22735
  have htrace : WordTrace (prefixWord ++ tailWord_22735) baseStart_22735 baseEnd_22735 := by
    simpa [prefixWord, tailWord_22735, baseEnd_22735] using wordTrace_append hprefix tailTrace_22735
  have hstable : (prefixWord ++ tailWord_22735).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22735).length < 2 ^ (prefixWord ++ tailWord_22735).sum := by decide
  have hdescent : baseEnd_22735 < baseStart_22735 := by decide
  rcases family_descends (prefixWord ++ tailWord_22735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22737 : List Nat := [1, 2, 2, 1, 2, 2, 2, 7]
def baseStart_22737 : Nat := 118140960795 + 22737 * 2 ^ 59
def prefixEnd_22737 : Nat := 4983230072969 + 3 ^ 40 * 22737 * 2
def baseEnd_22737 : Nat := 6918524231930533382483

theorem tailTrace_22737 : CollatzResearch.WordTrace tailWord_22737 prefixEnd_22737 6918524231930533382483 := by
  unfold tailWord_22737
  simp only [CollatzResearch.WordTrace]
  refine ⟨829286518635207015554465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 552857679090138010369643 829286518635207015554465)
  ·
    refine ⟨621964888976405261665849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 829286518635207015554465 621964888976405261665849)
    ·
      refine ⟨466473666732303946249387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 621964888976405261665849 466473666732303946249387)
      ·
        refine ⟨699710500098455919374081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 466473666732303946249387 699710500098455919374081)
        ·
          refine ⟨524782875073841939530561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 699710500098455919374081 524782875073841939530561)
          ·
            refine ⟨393587156305381454647921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 524782875073841939530561 393587156305381454647921)
            ·
              refine ⟨295190367229036090985941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 393587156305381454647921 295190367229036090985941)
              ·
                refine ⟨6918524231930533382483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 295190367229036090985941 6918524231930533382483)
                ·
                  rfl

theorem cell19_22737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 7].length) (baseStart_22737 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_22737 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_22737 prefixEnd_22737 := by exact prefixLift 22737
  have htrace : WordTrace (prefixWord ++ tailWord_22737) baseStart_22737 baseEnd_22737 := by
    simpa [prefixWord, tailWord_22737, baseEnd_22737] using wordTrace_append hprefix tailTrace_22737
  have hstable : (prefixWord ++ tailWord_22737).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22737).length < 2 ^ (prefixWord ++ tailWord_22737).sum := by decide
  have hdescent : baseEnd_22737 < baseStart_22737 := by decide
  rcases family_descends (prefixWord ++ tailWord_22737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22788 : List Nat := [2, 3, 2, 2, 3, 2, 2, 3]
def baseStart_22788 : Nat := 118140960795 + 22788 * 2 ^ 59
def prefixEnd_22788 : Nat := 4983230072969 + 3 ^ 40 * 22788 * 2
def baseEnd_22788 : Nat := 6934042758377526249011

theorem tailTrace_22788 : CollatzResearch.WordTrace tailWord_22788 prefixEnd_22788 6934042758377526249011 := by
  unfold tailWord_22788
  simp only [CollatzResearch.WordTrace]
  refine ⟨415573320725221362830509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 554097760966961817107345 415573320725221362830509)
  ·
    refine ⟨155839995271958011061441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 415573320725221362830509 155839995271958011061441)
    ·
      refine ⟨116879996453968508296081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155839995271958011061441 116879996453968508296081)
      ·
        refine ⟨87659997340476381222061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116879996453968508296081 87659997340476381222061)
        ·
          refine ⟨32872499002678642958273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87659997340476381222061 32872499002678642958273)
          ·
            refine ⟨24654374252008982218705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32872499002678642958273 24654374252008982218705)
            ·
              refine ⟨18490780689006736664029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24654374252008982218705 18490780689006736664029)
              ·
                refine ⟨6934042758377526249011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18490780689006736664029 6934042758377526249011)
                ·
                  rfl

theorem cell19_22788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 3].length) (baseStart_22788 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_22788 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_22788 prefixEnd_22788 := by exact prefixLift 22788
  have htrace : WordTrace (prefixWord ++ tailWord_22788) baseStart_22788 baseEnd_22788 := by
    simpa [prefixWord, tailWord_22788, baseEnd_22788] using wordTrace_append hprefix tailTrace_22788
  have hstable : (prefixWord ++ tailWord_22788).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22788).length < 2 ^ (prefixWord ++ tailWord_22788).sum := by decide
  have hdescent : baseEnd_22788 < baseStart_22788 := by decide
  rcases family_descends (prefixWord ++ tailWord_22788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22792 : List Nat := [2, 1, 3, 2, 3, 2, 1, 5]
def baseStart_22792 : Nat := 118140960795 + 22792 * 2 ^ 59
def prefixEnd_22792 : Nat := 4983230072969 + 3 ^ 40 * 22792 * 2
def baseEnd_22792 : Nat := 6935259897706702160111

theorem tailTrace_22792 : CollatzResearch.WordTrace tailWord_22792 prefixEnd_22792 6935259897706702160111 := by
  unfold tailWord_22792
  simp only [CollatzResearch.WordTrace]
  refine ⟨415646266717975704403315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 554195022290634272537753 415646266717975704403315)
  ·
    refine ⟨623469400076963556604973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 415646266717975704403315 623469400076963556604973)
    ·
      refine ⟨233801025028861333726865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 623469400076963556604973 233801025028861333726865)
      ·
        refine ⟨175350768771646000295149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233801025028861333726865 175350768771646000295149)
        ·
          refine ⟨65756538289367250110681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175350768771646000295149 65756538289367250110681)
          ·
            refine ⟨49317403717025437583011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65756538289367250110681 49317403717025437583011)
            ·
              refine ⟨73976105575538156374517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49317403717025437583011 73976105575538156374517)
              ·
                refine ⟨6935259897706702160111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73976105575538156374517 6935259897706702160111)
                ·
                  rfl

theorem cell19_22792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 5].length) (baseStart_22792 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_22792 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_22792 prefixEnd_22792 := by exact prefixLift 22792
  have htrace : WordTrace (prefixWord ++ tailWord_22792) baseStart_22792 baseEnd_22792 := by
    simpa [prefixWord, tailWord_22792, baseEnd_22792] using wordTrace_append hprefix tailTrace_22792
  have hstable : (prefixWord ++ tailWord_22792).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22792).length < 2 ^ (prefixWord ++ tailWord_22792).sum := by decide
  have hdescent : baseEnd_22792 < baseStart_22792 := by decide
  rcases family_descends (prefixWord ++ tailWord_22792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22851 : List Nat := [1, 1, 1, 3, 1, 3, 4, 5]
def baseStart_22851 : Nat := 118140960795 + 22851 * 2 ^ 59
def prefixEnd_22851 : Nat := 4983230072969 + 3 ^ 40 * 22851 * 2
def baseEnd_22851 : Nat := 6953212702812046848839

theorem tailTrace_22851 : CollatzResearch.WordTrace tailWord_22851 prefixEnd_22851 6953212702812046848839 := by
  unfold tailWord_22851
  simp only [CollatzResearch.WordTrace]
  refine ⟨833444440222204485204407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 555629626814802990136271 833444440222204485204407)
  ·
    refine ⟨1250166660333306727806611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 833444440222204485204407 1250166660333306727806611)
    ·
      refine ⟨1875249990499960091709917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1250166660333306727806611 1875249990499960091709917)
      ·
        refine ⟨703218746437485034391219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1875249990499960091709917 703218746437485034391219)
        ·
          refine ⟨1054828119656227551586829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 703218746437485034391219 1054828119656227551586829)
          ·
            refine ⟨395560544871085331845061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1054828119656227551586829 395560544871085331845061)
            ·
              refine ⟨74167602163328499720949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 395560544871085331845061 74167602163328499720949)
              ·
                refine ⟨6953212702812046848839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74167602163328499720949 6953212702812046848839)
                ·
                  rfl

theorem cell19_22851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 5].length) (baseStart_22851 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_22851 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_22851 prefixEnd_22851 := by exact prefixLift 22851
  have htrace : WordTrace (prefixWord ++ tailWord_22851) baseStart_22851 baseEnd_22851 := by
    simpa [prefixWord, tailWord_22851, baseEnd_22851] using wordTrace_append hprefix tailTrace_22851
  have hstable : (prefixWord ++ tailWord_22851).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22851).length < 2 ^ (prefixWord ++ tailWord_22851).sum := by decide
  have hdescent : baseEnd_22851 < baseStart_22851 := by decide
  rcases family_descends (prefixWord ++ tailWord_22851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22887 : List Nat := [1, 1, 5, 1, 3, 1, 3, 4]
def baseStart_22887 : Nat := 118140960795 + 22887 * 2 ^ 59
def prefixEnd_22887 : Nat := 4983230072969 + 3 ^ 40 * 22887 * 2
def baseEnd_22887 : Nat := 6964166956774630048741

theorem tailTrace_22887 : CollatzResearch.WordTrace tailWord_22887 prefixEnd_22887 6964166956774630048741 := by
  unfold tailWord_22887
  simp only [CollatzResearch.WordTrace]
  refine ⟨834757468091782633514915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 556504978727855089009943 834757468091782633514915)
  ·
    refine ⟨1252136202137673950272373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 834757468091782633514915 1252136202137673950272373)
    ·
      refine ⟨117387768950406932838035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1252136202137673950272373 117387768950406932838035)
      ·
        refine ⟨176081653425610399257053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117387768950406932838035 176081653425610399257053)
        ·
          refine ⟨66030620034603899721395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176081653425610399257053 66030620034603899721395)
          ·
            refine ⟨99045930051905849582093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66030620034603899721395 99045930051905849582093)
            ·
              refine ⟨37142223769464693593285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99045930051905849582093 37142223769464693593285)
              ·
                refine ⟨6964166956774630048741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37142223769464693593285 6964166956774630048741)
                ·
                  rfl

theorem cell19_22887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 4].length) (baseStart_22887 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_22887 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_22887 prefixEnd_22887 := by exact prefixLift 22887
  have htrace : WordTrace (prefixWord ++ tailWord_22887) baseStart_22887 baseEnd_22887 := by
    simpa [prefixWord, tailWord_22887, baseEnd_22887] using wordTrace_append hprefix tailTrace_22887
  have hstable : (prefixWord ++ tailWord_22887).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22887).length < 2 ^ (prefixWord ++ tailWord_22887).sum := by decide
  have hdescent : baseEnd_22887 < baseStart_22887 := by decide
  rcases family_descends (prefixWord ++ tailWord_22887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22957 : List Nat := [1, 5, 2, 2, 3, 1, 2, 3]
def baseStart_22957 : Nat := 118140960795 + 22957 * 2 ^ 59
def prefixEnd_22957 : Nat := 4983230072969 + 3 ^ 40 * 22957 * 2
def baseEnd_22957 : Nat := 6985466895035208492995

theorem tailTrace_22957 : CollatzResearch.WordTrace tailWord_22957 prefixEnd_22957 6985466895035208492995 := by
  unfold tailWord_22957
  simp only [CollatzResearch.WordTrace]
  refine ⟨837310577838184588563125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 558207051892123059042083 837310577838184588563125)
  ·
    refine ⟨78497866672329805177793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 837310577838184588563125 78497866672329805177793)
    ·
      refine ⟨58873400004247353883345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78497866672329805177793 58873400004247353883345)
      ·
        refine ⟨44155050003185515412509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58873400004247353883345 44155050003185515412509)
        ·
          refine ⟨16558143751194568279691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44155050003185515412509 16558143751194568279691)
          ·
            refine ⟨24837215626791852419537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16558143751194568279691 24837215626791852419537)
            ·
              refine ⟨18627911720093889314653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24837215626791852419537 18627911720093889314653)
              ·
                refine ⟨6985466895035208492995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18627911720093889314653 6985466895035208492995)
                ·
                  rfl

theorem cell19_22957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 3].length) (baseStart_22957 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_22957 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_22957 prefixEnd_22957 := by exact prefixLift 22957
  have htrace : WordTrace (prefixWord ++ tailWord_22957) baseStart_22957 baseEnd_22957 := by
    simpa [prefixWord, tailWord_22957, baseEnd_22957] using wordTrace_append hprefix tailTrace_22957
  have hstable : (prefixWord ++ tailWord_22957).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22957).length < 2 ^ (prefixWord ++ tailWord_22957).sum := by decide
  have hdescent : baseEnd_22957 < baseStart_22957 := by decide
  rcases family_descends (prefixWord ++ tailWord_22957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22961 : List Nat := [1, 2, 2, 4, 1, 4, 2, 3]
def baseStart_22961 : Nat := 118140960795 + 22961 * 2 ^ 59
def prefixEnd_22961 : Nat := 4983230072969 + 3 ^ 40 * 22961 * 2
def baseEnd_22961 : Nat := 6986684034364384404095

theorem tailTrace_22961 : CollatzResearch.WordTrace tailWord_22961 prefixEnd_22961 6986684034364384404095 := by
  unfold tailWord_22961
  simp only [CollatzResearch.WordTrace]
  refine ⟨837456469823693271708737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 558304313215795514472491 837456469823693271708737)
  ·
    refine ⟨628092352367769953781553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 837456469823693271708737 628092352367769953781553)
    ·
      refine ⟨471069264275827465336165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 628092352367769953781553 471069264275827465336165)
      ·
        refine ⟨88325487051717649750531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 471069264275827465336165 88325487051717649750531)
        ·
          refine ⟨132488230577576474625797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88325487051717649750531 132488230577576474625797)
          ·
            refine ⟨24841543233295588992337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132488230577576474625797 24841543233295588992337)
            ·
              refine ⟨18631157424971691744253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24841543233295588992337 18631157424971691744253)
              ·
                refine ⟨6986684034364384404095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18631157424971691744253 6986684034364384404095)
                ·
                  rfl

theorem cell19_22961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 3].length) (baseStart_22961 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_22961 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_22961 prefixEnd_22961 := by exact prefixLift 22961
  have htrace : WordTrace (prefixWord ++ tailWord_22961) baseStart_22961 baseEnd_22961 := by
    simpa [prefixWord, tailWord_22961, baseEnd_22961] using wordTrace_append hprefix tailTrace_22961
  have hstable : (prefixWord ++ tailWord_22961).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22961).length < 2 ^ (prefixWord ++ tailWord_22961).sum := by decide
  have hdescent : baseEnd_22961 < baseStart_22961 := by decide
  rcases family_descends (prefixWord ++ tailWord_22961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22980 : List Nat := [2, 3, 3, 2, 2, 2, 5]
def baseStart_22980 : Nat := 118140960795 + 22980 * 2 ^ 59
def prefixEnd_22980 : Nat := 4983230072969 + 3 ^ 40 * 22980 * 2
def baseEnd_22980 : Nat := 2330821815392656660607

theorem tailTrace_22980 : CollatzResearch.WordTrace tailWord_22980 prefixEnd_22980 2330821815392656660607 := by
  unfold tailWord_22980
  simp only [CollatzResearch.WordTrace]
  refine ⟨419074728377429758325197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 558766304503239677766929 419074728377429758325197)
  ·
    refine ⟨157153023141536159371949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 419074728377429758325197 157153023141536159371949)
    ·
      refine ⟨58932383678076059764481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157153023141536159371949 58932383678076059764481)
      ·
        refine ⟨44199287758557044823361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58932383678076059764481 44199287758557044823361)
        ·
          refine ⟨33149465818917783617521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44199287758557044823361 33149465818917783617521)
          ·
            refine ⟨24862099364188337713141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33149465818917783617521 24862099364188337713141)
            ·
              refine ⟨2330821815392656660607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24862099364188337713141 2330821815392656660607)
              ·
                rfl

theorem cell19_22980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 5].length) (baseStart_22980 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_22980 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_22980 prefixEnd_22980 := by exact prefixLift 22980
  have htrace : WordTrace (prefixWord ++ tailWord_22980) baseStart_22980 baseEnd_22980 := by
    simpa [prefixWord, tailWord_22980, baseEnd_22980] using wordTrace_append hprefix tailTrace_22980
  have hstable : (prefixWord ++ tailWord_22980).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22980).length < 2 ^ (prefixWord ++ tailWord_22980).sum := by decide
  have hdescent : baseEnd_22980 < baseStart_22980 := by decide
  rcases family_descends (prefixWord ++ tailWord_22980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_22984 : List Nat := [2, 1, 3, 1, 3, 2, 7]
def baseStart_22984 : Nat := 118140960795 + 22984 * 2 ^ 59
def prefixEnd_22984 : Nat := 4983230072969 + 3 ^ 40 * 22984 * 2
def baseEnd_22984 : Nat := 2331227528502381964307

theorem tailTrace_22984 : CollatzResearch.WordTrace tailWord_22984 prefixEnd_22984 2331227528502381964307 := by
  unfold tailWord_22984
  simp only [CollatzResearch.WordTrace]
  refine ⟨419147674370184099898003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 558863565826912133197337 419147674370184099898003)
  ·
    refine ⟨628721511555276149847005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 419147674370184099898003 628721511555276149847005)
    ·
      refine ⟨235770566833228556192627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 628721511555276149847005 235770566833228556192627)
      ·
        refine ⟨353655850249842834288941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235770566833228556192627 353655850249842834288941)
        ·
          refine ⟨132620943843691062858353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 353655850249842834288941 132620943843691062858353)
          ·
            refine ⟨99465707882768297143765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132620943843691062858353 99465707882768297143765)
            ·
              refine ⟨2331227528502381964307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 99465707882768297143765 2331227528502381964307)
              ·
                rfl

theorem cell19_22984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 7].length) (baseStart_22984 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_22984 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_22984 prefixEnd_22984 := by exact prefixLift 22984
  have htrace : WordTrace (prefixWord ++ tailWord_22984) baseStart_22984 baseEnd_22984 := by
    simpa [prefixWord, tailWord_22984, baseEnd_22984] using wordTrace_append hprefix tailTrace_22984
  have hstable : (prefixWord ++ tailWord_22984).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_22984).length < 2 ^ (prefixWord ++ tailWord_22984).sum := by decide
  have hdescent : baseEnd_22984 < baseStart_22984 := by decide
  rcases family_descends (prefixWord ++ tailWord_22984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23041 : List Nat := [1, 2, 4, 1, 3, 8]
def baseStart_23041 : Nat := 118140960795 + 23041 * 2 ^ 59
def prefixEnd_23041 : Nat := 4983230072969 + 3 ^ 40 * 23041 * 2
def baseEnd_23041 : Nat := 779002980105322514011

theorem tailTrace_23041 : CollatzResearch.WordTrace tailWord_23041 prefixEnd_23041 779002980105322514011 := by
  unfold tailWord_23041
  simp only [CollatzResearch.WordTrace]
  refine ⟨840374309533866934620977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 560249539689244623080651 840374309533866934620977)
  ·
    refine ⟨630280732150400200965733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 840374309533866934620977 630280732150400200965733)
    ·
      refine ⟨118177637278200037681075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 630280732150400200965733 118177637278200037681075)
      ·
        refine ⟨177266455917300056521613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118177637278200037681075 177266455917300056521613)
        ·
          refine ⟨66474920968987521195605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177266455917300056521613 66474920968987521195605)
          ·
            refine ⟨779002980105322514011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 66474920968987521195605 779002980105322514011)
            ·
              rfl

theorem cell19_23041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 8].length) (baseStart_23041 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_23041 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_23041 prefixEnd_23041 := by exact prefixLift 23041
  have htrace : WordTrace (prefixWord ++ tailWord_23041) baseStart_23041 baseEnd_23041 := by
    simpa [prefixWord, tailWord_23041, baseEnd_23041] using wordTrace_append hprefix tailTrace_23041
  have hstable : (prefixWord ++ tailWord_23041).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23041).length < 2 ^ (prefixWord ++ tailWord_23041).sum := by decide
  have hdescent : baseEnd_23041 < baseStart_23041 := by decide
  rcases family_descends (prefixWord ++ tailWord_23041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23098 : List Nat := [3, 1, 1, 1, 3, 4, 6]
def baseStart_23098 : Nat := 118140960795 + 23098 * 2 ^ 59
def prefixEnd_23098 : Nat := 4983230072969 + 3 ^ 40 * 23098 * 2
def baseEnd_23098 : Nat := 2342790352129553119759

theorem tailTrace_23098 : CollatzResearch.WordTrace tailWord_23098 prefixEnd_23098 2342790352129553119759 := by
  unfold tailWord_23098
  simp only [CollatzResearch.WordTrace]
  refine ⟨210613317581841417361487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 561635513551577112963965 210613317581841417361487)
  ·
    refine ⟨315919976372762126042231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210613317581841417361487 315919976372762126042231)
    ·
      refine ⟨473879964559143189063347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315919976372762126042231 473879964559143189063347)
      ·
        refine ⟨710819946838714783595021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 473879964559143189063347 710819946838714783595021)
        ·
          refine ⟨266557480064518043848133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 710819946838714783595021 266557480064518043848133)
          ·
            refine ⟨49979527512097133221525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 266557480064518043848133 49979527512097133221525)
            ·
              refine ⟨2342790352129553119759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 49979527512097133221525 2342790352129553119759)
              ·
                rfl

theorem cell19_23098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 6].length) (baseStart_23098 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_23098 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_23098 prefixEnd_23098 := by exact prefixLift 23098
  have htrace : WordTrace (prefixWord ++ tailWord_23098) baseStart_23098 baseEnd_23098 := by
    simpa [prefixWord, tailWord_23098, baseEnd_23098] using wordTrace_append hprefix tailTrace_23098
  have hstable : (prefixWord ++ tailWord_23098).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23098).length < 2 ^ (prefixWord ++ tailWord_23098).sum := by decide
  have hdescent : baseEnd_23098 < baseStart_23098 := by decide
  rcases family_descends (prefixWord ++ tailWord_23098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23172 : List Nat := [2, 3, 2, 1, 3, 2, 2, 4]
def baseStart_23172 : Nat := 118140960795 + 23172 * 2 ^ 59
def prefixEnd_23172 : Nat := 4983230072969 + 3 ^ 40 * 23172 * 2
def baseEnd_23172 : Nat := 7050888133978413714631

theorem tailTrace_23172 : CollatzResearch.WordTrace tailWord_23172 prefixEnd_23172 7050888133978413714631 := by
  unfold tailWord_23172
  simp only [CollatzResearch.WordTrace]
  refine ⟨422576136029638153819885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 563434848039517538426513 422576136029638153819885)
  ·
    refine ⟨158466051011114307682457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 422576136029638153819885 158466051011114307682457)
    ·
      refine ⟨118849538258335730761843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158466051011114307682457 118849538258335730761843)
      ·
        refine ⟨178274307387503596142765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118849538258335730761843 178274307387503596142765)
        ·
          refine ⟨66852865270313848553537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178274307387503596142765 66852865270313848553537)
          ·
            refine ⟨50139648952735386415153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66852865270313848553537 50139648952735386415153)
            ·
              refine ⟨37604736714551539811365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50139648952735386415153 37604736714551539811365)
              ·
                refine ⟨7050888133978413714631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37604736714551539811365 7050888133978413714631)
                ·
                  rfl

theorem cell19_23172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 4].length) (baseStart_23172 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_23172 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_23172 prefixEnd_23172 := by exact prefixLift 23172
  have htrace : WordTrace (prefixWord ++ tailWord_23172) baseStart_23172 baseEnd_23172 := by
    simpa [prefixWord, tailWord_23172, baseEnd_23172] using wordTrace_append hprefix tailTrace_23172
  have hstable : (prefixWord ++ tailWord_23172).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23172).length < 2 ^ (prefixWord ++ tailWord_23172).sum := by decide
  have hdescent : baseEnd_23172 < baseStart_23172 := by decide
  rcases family_descends (prefixWord ++ tailWord_23172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23210 : List Nat := [3, 1, 5, 2, 8]
def baseStart_23210 : Nat := 118140960795 + 23210 * 2 ^ 59
def prefixEnd_23210 : Nat := 4983230072969 + 3 ^ 40 * 23210 * 2
def baseEnd_23210 : Nat := 261572257689095735929

theorem tailTrace_23210 : CollatzResearch.WordTrace tailWord_23210 prefixEnd_23210 261572257689095735929 := by
  unfold tailWord_23210
  simp only [CollatzResearch.WordTrace]
  refine ⟨211634561480402199380771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 564358830614405865015389 211634561480402199380771)
  ·
    refine ⟨317451842220603299071157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211634561480402199380771 317451842220603299071157)
    ·
      refine ⟨29761110208181559287921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 317451842220603299071157 29761110208181559287921)
      ·
        refine ⟨22320832656136169465941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29761110208181559287921 22320832656136169465941)
        ·
          refine ⟨261572257689095735929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 22320832656136169465941 261572257689095735929)
          ·
            rfl

theorem cell19_23210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 8].length) (baseStart_23210 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_23210 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_23210 prefixEnd_23210 := by exact prefixLift 23210
  have htrace : WordTrace (prefixWord ++ tailWord_23210) baseStart_23210 baseEnd_23210 := by
    simpa [prefixWord, tailWord_23210, baseEnd_23210] using wordTrace_append hprefix tailTrace_23210
  have hstable : (prefixWord ++ tailWord_23210).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23210).length < 2 ^ (prefixWord ++ tailWord_23210).sum := by decide
  have hdescent : baseEnd_23210 < baseStart_23210 := by decide
  rcases family_descends (prefixWord ++ tailWord_23210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23229 : List Nat := [1, 4, 1, 2, 1, 5, 1, 4]
def baseStart_23229 : Nat := 118140960795 + 23229 * 2 ^ 59
def prefixEnd_23229 : Nat := 4983230072969 + 3 ^ 40 * 23229 * 2
def baseEnd_23229 : Nat := 7068232369419170447809

theorem tailTrace_23229 : CollatzResearch.WordTrace tailWord_23229 prefixEnd_23229 7068232369419170447809 := by
  unfold tailWord_23229
  simp only [CollatzResearch.WordTrace]
  refine ⟨847231232852775042464741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 564820821901850028309827 847231232852775042464741)
  ·
    refine ⟨158855856159895320462139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 847231232852775042464741 158855856159895320462139)
    ·
      refine ⟨238283784239842980693209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158855856159895320462139 238283784239842980693209)
      ·
        refine ⟨178712838179882235519907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238283784239842980693209 178712838179882235519907)
        ·
          refine ⟨268069257269823353279861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178712838179882235519907 268069257269823353279861)
          ·
            refine ⟨25131492869045939369987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 268069257269823353279861 25131492869045939369987)
            ·
              refine ⟨37697239303568909054981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25131492869045939369987 37697239303568909054981)
              ·
                refine ⟨7068232369419170447809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37697239303568909054981 7068232369419170447809)
                ·
                  rfl

theorem cell19_23229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 4].length) (baseStart_23229 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_23229 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_23229 prefixEnd_23229 := by exact prefixLift 23229
  have htrace : WordTrace (prefixWord ++ tailWord_23229) baseStart_23229 baseEnd_23229 := by
    simpa [prefixWord, tailWord_23229, baseEnd_23229] using wordTrace_append hprefix tailTrace_23229
  have hstable : (prefixWord ++ tailWord_23229).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23229).length < 2 ^ (prefixWord ++ tailWord_23229).sum := by decide
  have hdescent : baseEnd_23229 < baseStart_23229 := by decide
  rcases family_descends (prefixWord ++ tailWord_23229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23231 : List Nat := [1, 1, 2, 2, 2, 4, 3, 4]
def baseStart_23231 : Nat := 118140960795 + 23231 * 2 ^ 59
def prefixEnd_23231 : Nat := 4983230072969 + 3 ^ 40 * 23231 * 2
def baseEnd_23231 : Nat := 7068840939083758403359

theorem tailTrace_23231 : CollatzResearch.WordTrace tailWord_23231 prefixEnd_23231 7068840939083758403359 := by
  unfold tailWord_23231
  simp only [CollatzResearch.WordTrace]
  refine ⟨847304178845529384037547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 564869452563686256025031 847304178845529384037547)
  ·
    refine ⟨1270956268268294076056321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 847304178845529384037547 1270956268268294076056321)
    ·
      refine ⟨953217201201220557042241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1270956268268294076056321 953217201201220557042241)
      ·
        refine ⟨714912900900915417781681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 953217201201220557042241 714912900900915417781681)
        ·
          refine ⟨536184675675686563336261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 714912900900915417781681 536184675675686563336261)
          ·
            refine ⟨100534626689191230625549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 536184675675686563336261 100534626689191230625549)
            ·
              refine ⟨37700485008446711484581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100534626689191230625549 37700485008446711484581)
              ·
                refine ⟨7068840939083758403359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37700485008446711484581 7068840939083758403359)
                ·
                  rfl

theorem cell19_23231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 4].length) (baseStart_23231 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_23231 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_23231 prefixEnd_23231 := by exact prefixLift 23231
  have htrace : WordTrace (prefixWord ++ tailWord_23231) baseStart_23231 baseEnd_23231 := by
    simpa [prefixWord, tailWord_23231, baseEnd_23231] using wordTrace_append hprefix tailTrace_23231
  have hstable : (prefixWord ++ tailWord_23231).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23231).length < 2 ^ (prefixWord ++ tailWord_23231).sum := by decide
  have hdescent : baseEnd_23231 < baseStart_23231 := by decide
  rcases family_descends (prefixWord ++ tailWord_23231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23269 : List Nat := [1, 3, 1, 4, 1, 3, 6]
def baseStart_23269 : Nat := 118140960795 + 23269 * 2 ^ 59
def prefixEnd_23269 : Nat := 4983230072969 + 3 ^ 40 * 23269 * 2
def baseEnd_23269 : Nat := 2360134587570309852937

theorem tailTrace_23269 : CollatzResearch.WordTrace tailWord_23269 prefixEnd_23269 2360134587570309852937 := by
  unfold tailWord_23269
  simp only [CollatzResearch.WordTrace]
  refine ⟨848690152707861873920861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 565793435138574582613907 848690152707861873920861)
  ·
    refine ⟨318258807265448202720323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 848690152707861873920861 318258807265448202720323)
    ·
      refine ⟨477388210898172304080485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318258807265448202720323 477388210898172304080485)
      ·
        refine ⟨89510289543407307015091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 477388210898172304080485 89510289543407307015091)
        ·
          refine ⟨134265434315110960522637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89510289543407307015091 134265434315110960522637)
          ·
            refine ⟨50349537868166610195989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134265434315110960522637 50349537868166610195989)
            ·
              refine ⟨2360134587570309852937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 50349537868166610195989 2360134587570309852937)
              ·
                rfl

theorem cell19_23269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 6].length) (baseStart_23269 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_23269 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_23269 prefixEnd_23269 := by exact prefixLift 23269
  have htrace : WordTrace (prefixWord ++ tailWord_23269) baseStart_23269 baseEnd_23269 := by
    simpa [prefixWord, tailWord_23269, baseEnd_23269] using wordTrace_append hprefix tailTrace_23269
  have hstable : (prefixWord ++ tailWord_23269).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23269).length < 2 ^ (prefixWord ++ tailWord_23269).sum := by decide
  have hdescent : baseEnd_23269 < baseStart_23269 := by decide
  rcases family_descends (prefixWord ++ tailWord_23269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23303 : List Nat := [1, 1, 4, 4, 1, 3, 2, 3]
def baseStart_23303 : Nat := 118140960795 + 23303 * 2 ^ 59
def prefixEnd_23303 : Nat := 4983230072969 + 3 ^ 40 * 23303 * 2
def baseEnd_23303 : Nat := 7090749447008924803163

theorem tailTrace_23303 : CollatzResearch.WordTrace tailWord_23303 prefixEnd_23303 7090749447008924803163 := by
  unfold tailWord_23303
  simp only [CollatzResearch.WordTrace]
  refine ⟨849930234584685680658563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 566620156389790453772375 849930234584685680658563)
  ·
    refine ⟨1274895351877028520987845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 849930234584685680658563 1274895351877028520987845)
    ·
      refine ⟨239042878476942847685221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1274895351877028520987845 239042878476942847685221)
      ·
        refine ⟨44820539714426783940979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 239042878476942847685221 44820539714426783940979)
        ·
          refine ⟨67230809571640175911469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44820539714426783940979 67230809571640175911469)
          ·
            refine ⟨25211553589365065966801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67230809571640175911469 25211553589365065966801)
            ·
              refine ⟨18908665192023799475101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25211553589365065966801 18908665192023799475101)
              ·
                refine ⟨7090749447008924803163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18908665192023799475101 7090749447008924803163)
                ·
                  rfl

theorem cell19_23303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 3].length) (baseStart_23303 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_23303 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_23303 prefixEnd_23303 := by exact prefixLift 23303
  have htrace : WordTrace (prefixWord ++ tailWord_23303) baseStart_23303 baseEnd_23303 := by
    simpa [prefixWord, tailWord_23303, baseEnd_23303] using wordTrace_append hprefix tailTrace_23303
  have hstable : (prefixWord ++ tailWord_23303).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23303).length < 2 ^ (prefixWord ++ tailWord_23303).sum := by decide
  have hdescent : baseEnd_23303 < baseStart_23303 := by decide
  rcases family_descends (prefixWord ++ tailWord_23303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23345 : List Nat := [1, 2, 2, 3, 2, 1, 4, 4]
def baseStart_23345 : Nat := 118140960795 + 23345 * 2 ^ 59
def prefixEnd_23345 : Nat := 4983230072969 + 3 ^ 40 * 23345 * 2
def baseEnd_23345 : Nat := 7103529409965271869715

theorem tailTrace_23345 : CollatzResearch.WordTrace tailWord_23345 prefixEnd_23345 7103529409965271869715 := by
  unfold tailWord_23345
  simp only [CollatzResearch.WordTrace]
  refine ⟨851462100432526853687489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 567641400288351235791659 851462100432526853687489)
  ·
    refine ⟨638596575324395140265617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 851462100432526853687489 638596575324395140265617)
    ·
      refine ⟨478947431493296355199213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 638596575324395140265617 478947431493296355199213)
      ·
        refine ⟨179605286809986133199705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 478947431493296355199213 179605286809986133199705)
        ·
          refine ⟨134703965107489599899779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179605286809986133199705 134703965107489599899779)
          ·
            refine ⟨202055947661234399849669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134703965107489599899779 202055947661234399849669)
            ·
              refine ⟨37885490186481449971813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 202055947661234399849669 37885490186481449971813)
              ·
                refine ⟨7103529409965271869715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37885490186481449971813 7103529409965271869715)
                ·
                  rfl

theorem cell19_23345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 4].length) (baseStart_23345 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_23345 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_23345 prefixEnd_23345 := by exact prefixLift 23345
  have htrace : WordTrace (prefixWord ++ tailWord_23345) baseStart_23345 baseEnd_23345 := by
    simpa [prefixWord, tailWord_23345, baseEnd_23345] using wordTrace_append hprefix tailTrace_23345
  have hstable : (prefixWord ++ tailWord_23345).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23345).length < 2 ^ (prefixWord ++ tailWord_23345).sum := by decide
  have hdescent : baseEnd_23345 < baseStart_23345 := by decide
  rcases family_descends (prefixWord ++ tailWord_23345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23385 : List Nat := [1, 2, 1, 2, 2, 11]
def baseStart_23385 : Nat := 118140960795 + 23385 * 2 ^ 59
def prefixEnd_23385 : Nat := 4983230072969 + 3 ^ 40 * 23385 * 2
def baseEnd_23385 : Nat := 790633422584114553413

theorem tailTrace_23385 : CollatzResearch.WordTrace tailWord_23385 prefixEnd_23385 790633422584114553413 := by
  unfold tailWord_23385
  simp only [CollatzResearch.WordTrace]
  refine ⟨852921020287613685143609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 568614013525075790095739 852921020287613685143609)
  ·
    refine ⟨639690765215710263857707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 852921020287613685143609 639690765215710263857707)
    ·
      refine ⟨959536147823565395786561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 639690765215710263857707 959536147823565395786561)
      ·
        refine ⟨719652110867674046839921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 959536147823565395786561 719652110867674046839921)
        ·
          refine ⟨539739083150755535129941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 719652110867674046839921 539739083150755535129941)
          ·
            refine ⟨790633422584114553413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 539739083150755535129941 790633422584114553413)
            ·
              rfl

theorem cell19_23385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 11].length) (baseStart_23385 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_23385 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_23385 prefixEnd_23385 := by exact prefixLift 23385
  have htrace : WordTrace (prefixWord ++ tailWord_23385) baseStart_23385 baseEnd_23385 := by
    simpa [prefixWord, tailWord_23385, baseEnd_23385] using wordTrace_append hprefix tailTrace_23385
  have hstable : (prefixWord ++ tailWord_23385).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23385).length < 2 ^ (prefixWord ++ tailWord_23385).sum := by decide
  have hdescent : baseEnd_23385 < baseStart_23385 := by decide
  rcases family_descends (prefixWord ++ tailWord_23385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23400 : List Nat := [2, 1, 4, 2, 1, 4, 1, 4]
def baseStart_23400 : Nat := 118140960795 + 23400 * 2 ^ 59
def prefixEnd_23400 : Nat := 4983230072969 + 3 ^ 40 * 23400 * 2
def baseEnd_23400 : Nat := 7120265075741440647343

theorem tailTrace_23400 : CollatzResearch.WordTrace tailWord_23400 prefixEnd_23400 7120265075741440647343 := by
  unfold tailWord_23400
  simp only [CollatzResearch.WordTrace]
  refine ⟨426734057616635623469827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 568978743488847497959769 426734057616635623469827)
  ·
    refine ⟨640101086424953435204741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 426734057616635623469827 640101086424953435204741)
    ·
      refine ⟨120018953704678769100889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 640101086424953435204741 120018953704678769100889)
      ·
        refine ⟨90014215278509076825667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120018953704678769100889 90014215278509076825667)
        ·
          refine ⟨135021322917763615238501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90014215278509076825667 135021322917763615238501)
          ·
            refine ⟨25316498047080677857219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135021322917763615238501 25316498047080677857219)
            ·
              refine ⟨37974747070621016785829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25316498047080677857219 37974747070621016785829)
              ·
                refine ⟨7120265075741440647343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37974747070621016785829 7120265075741440647343)
                ·
                  rfl

theorem cell19_23400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 4].length) (baseStart_23400 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_23400 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_23400 prefixEnd_23400 := by exact prefixLift 23400
  have htrace : WordTrace (prefixWord ++ tailWord_23400) baseStart_23400 baseEnd_23400 := by
    simpa [prefixWord, tailWord_23400, baseEnd_23400] using wordTrace_append hprefix tailTrace_23400
  have hstable : (prefixWord ++ tailWord_23400).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23400).length < 2 ^ (prefixWord ++ tailWord_23400).sum := by decide
  have hdescent : baseEnd_23400 < baseStart_23400 := by decide
  rcases family_descends (prefixWord ++ tailWord_23400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23423 : List Nat := [1, 1, 2, 2, 1, 1, 4, 7]
def baseStart_23423 : Nat := 118140960795 + 23423 * 2 ^ 59
def prefixEnd_23423 : Nat := 4983230072969 + 3 ^ 40 * 23423 * 2
def baseEnd_23423 : Nat := 7127263626884202136169

theorem tailTrace_23423 : CollatzResearch.WordTrace tailWord_23423 prefixEnd_23423 7127263626884202136169 := by
  unfold tailWord_23423
  simp only [CollatzResearch.WordTrace]
  refine ⟨854306994149946175026923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 569537996099964116684615 854306994149946175026923)
  ·
    refine ⟨1281460491224919262540385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 854306994149946175026923 1281460491224919262540385)
    ·
      refine ⟨961095368418689446905289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1281460491224919262540385 961095368418689446905289)
      ·
        refine ⟨720821526314017085178967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 961095368418689446905289 720821526314017085178967)
        ·
          refine ⟨1081232289471025627768451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 720821526314017085178967 1081232289471025627768451)
          ·
            refine ⟨1621848434206538441652677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1081232289471025627768451 1621848434206538441652677)
            ·
              refine ⟨304096581413725957809877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1621848434206538441652677 304096581413725957809877)
              ·
                refine ⟨7127263626884202136169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 304096581413725957809877 7127263626884202136169)
                ·
                  rfl

theorem cell19_23423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 7].length) (baseStart_23423 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_23423 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_23423 prefixEnd_23423 := by exact prefixLift 23423
  have htrace : WordTrace (prefixWord ++ tailWord_23423) baseStart_23423 baseEnd_23423 := by
    simpa [prefixWord, tailWord_23423, baseEnd_23423] using wordTrace_append hprefix tailTrace_23423
  have hstable : (prefixWord ++ tailWord_23423).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23423).length < 2 ^ (prefixWord ++ tailWord_23423).sum := by decide
  have hdescent : baseEnd_23423 < baseStart_23423 := by decide
  rcases family_descends (prefixWord ++ tailWord_23423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23499 : List Nat := [1, 1, 1, 1, 3, 5, 7]
def baseStart_23499 : Nat := 118140960795 + 23499 * 2 ^ 59
def prefixEnd_23499 : Nat := 4983230072969 + 3 ^ 40 * 23499 * 2
def baseEnd_23499 : Nat := 2383463091379514815691

theorem tailTrace_23499 : CollatzResearch.WordTrace tailWord_23499 prefixEnd_23499 2383463091379514815691 := by
  unfold tailWord_23499
  simp only [CollatzResearch.WordTrace]
  refine ⟨857078941874611154793551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 571385961249740769862367 857078941874611154793551)
  ·
    refine ⟨1285618412811916732190327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 857078941874611154793551 1285618412811916732190327)
    ·
      refine ⟨1928427619217875098285491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1285618412811916732190327 1928427619217875098285491)
      ·
        refine ⟨2892641428826812647428237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1928427619217875098285491 2892641428826812647428237)
        ·
          refine ⟨1084740535810054742785589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2892641428826812647428237 1084740535810054742785589)
          ·
            refine ⟨101694425232192632136149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1084740535810054742785589 101694425232192632136149)
            ·
              refine ⟨2383463091379514815691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 101694425232192632136149 2383463091379514815691)
              ·
                rfl

theorem cell19_23499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 7].length) (baseStart_23499 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_23499 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_23499 prefixEnd_23499 := by exact prefixLift 23499
  have htrace : WordTrace (prefixWord ++ tailWord_23499) baseStart_23499 baseEnd_23499 := by
    simpa [prefixWord, tailWord_23499, baseEnd_23499] using wordTrace_append hprefix tailTrace_23499
  have hstable : (prefixWord ++ tailWord_23499).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23499).length < 2 ^ (prefixWord ++ tailWord_23499).sum := by decide
  have hdescent : baseEnd_23499 < baseStart_23499 := by decide
  rcases family_descends (prefixWord ++ tailWord_23499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23556 : List Nat := [2, 3, 2, 12]
def baseStart_23556 : Nat := 118140960795 + 23556 * 2 ^ 59
def prefixEnd_23556 : Nat := 4983230072969 + 3 ^ 40 * 23556 * 2
def baseEnd_23556 : Nat := 88490537155300014571

theorem tailTrace_23556 : CollatzResearch.WordTrace tailWord_23556 prefixEnd_23556 88490537155300014571 := by
  unfold tailWord_23556
  simp only [CollatzResearch.WordTrace]
  refine ⟨429578951334054944809261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 572771935112073259745681 429578951334054944809261)
  ·
    refine ⟨161092106750270604303473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 429578951334054944809261 161092106750270604303473)
    ·
      refine ⟨120819080062702953227605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161092106750270604303473 120819080062702953227605)
      ·
        refine ⟨88490537155300014571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 120819080062702953227605 88490537155300014571)
        ·
          rfl

theorem cell19_23556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 12].length) (baseStart_23556 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_23556 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_23556 prefixEnd_23556 := by exact prefixLift 23556
  have htrace : WordTrace (prefixWord ++ tailWord_23556) baseStart_23556 baseEnd_23556 := by
    simpa [prefixWord, tailWord_23556, baseEnd_23556] using wordTrace_append hprefix tailTrace_23556
  have hstable : (prefixWord ++ tailWord_23556).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23556).length < 2 ^ (prefixWord ++ tailWord_23556).sum := by decide
  have hdescent : baseEnd_23556 < baseStart_23556 := by decide
  rcases family_descends (prefixWord ++ tailWord_23556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23573 : List Nat := [1, 3, 2, 1, 4, 1, 3, 4]
def baseStart_23573 : Nat := 118140960795 + 23573 * 2 ^ 59
def prefixEnd_23573 : Nat := 4983230072969 + 3 ^ 40 * 23573 * 2
def baseEnd_23573 : Nat := 7172906351728298802427

theorem tailTrace_23573 : CollatzResearch.WordTrace tailWord_23573 prefixEnd_23573 7172906351728298802427 := by
  unfold tailWord_23573
  simp only [CollatzResearch.WordTrace]
  refine ⟨859777943606521792987373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 573185295737681195324915 859777943606521792987373)
  ·
    refine ⟨322416728852445672370265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 859777943606521792987373 322416728852445672370265)
    ·
      refine ⟨241812546639334254277699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 322416728852445672370265 241812546639334254277699)
      ·
        refine ⟨362718819959001381416549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241812546639334254277699 362718819959001381416549)
        ·
          refine ⟨68009778742312759015603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 362718819959001381416549 68009778742312759015603)
          ·
            refine ⟨102014668113469138523405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68009778742312759015603 102014668113469138523405)
            ·
              refine ⟨38255500542550926946277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102014668113469138523405 38255500542550926946277)
              ·
                refine ⟨7172906351728298802427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38255500542550926946277 7172906351728298802427)
                ·
                  rfl

theorem cell19_23573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 4].length) (baseStart_23573 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_23573 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_23573 prefixEnd_23573 := by exact prefixLift 23573
  have htrace : WordTrace (prefixWord ++ tailWord_23573) baseStart_23573 baseEnd_23573 := by
    simpa [prefixWord, tailWord_23573, baseEnd_23573] using wordTrace_append hprefix tailTrace_23573
  have hstable : (prefixWord ++ tailWord_23573).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23573).length < 2 ^ (prefixWord ++ tailWord_23573).sum := by decide
  have hdescent : baseEnd_23573 < baseStart_23573 := by decide
  rcases family_descends (prefixWord ++ tailWord_23573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23649 : List Nat := [1, 2, 3, 1, 1, 2, 6, 3]
def baseStart_23649 : Nat := 118140960795 + 23649 * 2 ^ 59
def prefixEnd_23649 : Nat := 4983230072969 + 3 ^ 40 * 23649 * 2
def baseEnd_23649 : Nat := 7196031998982641113331

theorem tailTrace_23649 : CollatzResearch.WordTrace tailWord_23649 prefixEnd_23649 7196031998982641113331 := by
  unfold tailWord_23649
  simp only [CollatzResearch.WordTrace]
  refine ⟨862549891331186772754001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 575033260887457848502667 862549891331186772754001)
  ·
    refine ⟨646912418498390079565501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 862549891331186772754001 646912418498390079565501)
    ·
      refine ⟨242592156936896279837063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 646912418498390079565501 242592156936896279837063)
      ·
        refine ⟨363888235405344419755595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242592156936896279837063 363888235405344419755595)
        ·
          refine ⟨545832353108016629633393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 363888235405344419755595 545832353108016629633393)
          ·
            refine ⟨409374264831012472225045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 545832353108016629633393 409374264831012472225045)
            ·
              refine ⟨19189418663953709635549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 409374264831012472225045 19189418663953709635549)
              ·
                refine ⟨7196031998982641113331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19189418663953709635549 7196031998982641113331)
                ·
                  rfl

theorem cell19_23649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 3].length) (baseStart_23649 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_23649 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_23649 prefixEnd_23649 := by exact prefixLift 23649
  have htrace : WordTrace (prefixWord ++ tailWord_23649) baseStart_23649 baseEnd_23649 := by
    simpa [prefixWord, tailWord_23649, baseEnd_23649] using wordTrace_append hprefix tailTrace_23649
  have hstable : (prefixWord ++ tailWord_23649).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23649).length < 2 ^ (prefixWord ++ tailWord_23649).sum := by decide
  have hdescent : baseEnd_23649 < baseStart_23649 := by decide
  rcases family_descends (prefixWord ++ tailWord_23649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23689 : List Nat := [1, 2, 1, 1, 4, 3, 1, 6]
def baseStart_23689 : Nat := 118140960795 + 23689 * 2 ^ 59
def prefixEnd_23689 : Nat := 4983230072969 + 3 ^ 40 * 23689 * 2
def baseEnd_23689 : Nat := 7208203392274400224333

theorem tailTrace_23689 : CollatzResearch.WordTrace tailWord_23689 prefixEnd_23689 7208203392274400224333 := by
  unfold tailWord_23689
  simp only [CollatzResearch.WordTrace]
  refine ⟨864008811186273604210121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 576005874124182402806747 864008811186273604210121)
  ·
    refine ⟨648006608389705203157591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 864008811186273604210121 648006608389705203157591)
    ·
      refine ⟨972009912584557804736387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 648006608389705203157591 972009912584557804736387)
      ·
        refine ⟨1458014868876836707104581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 972009912584557804736387 1458014868876836707104581)
        ·
          refine ⟨273377787914406882582109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1458014868876836707104581 273377787914406882582109)
          ·
            refine ⟨102516670467902580968291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 273377787914406882582109 102516670467902580968291)
            ·
              refine ⟨153775005701853871452437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102516670467902580968291 153775005701853871452437)
              ·
                refine ⟨7208203392274400224333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 153775005701853871452437 7208203392274400224333)
                ·
                  rfl

theorem cell19_23689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 6].length) (baseStart_23689 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_23689 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_23689 prefixEnd_23689 := by exact prefixLift 23689
  have htrace : WordTrace (prefixWord ++ tailWord_23689) baseStart_23689 baseEnd_23689 := by
    simpa [prefixWord, tailWord_23689, baseEnd_23689] using wordTrace_append hprefix tailTrace_23689
  have hstable : (prefixWord ++ tailWord_23689).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23689).length < 2 ^ (prefixWord ++ tailWord_23689).sum := by decide
  have hdescent : baseEnd_23689 < baseStart_23689 := by decide
  rcases family_descends (prefixWord ++ tailWord_23689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23706 : List Nat := [3, 1, 1, 5, 1, 1, 2, 5]
def baseStart_23706 : Nat := 118140960795 + 23706 * 2 ^ 59
def prefixEnd_23706 : Nat := 4983230072969 + 3 ^ 40 * 23706 * 2
def baseEnd_23706 : Nat := 7213376234423397846509

theorem tailTrace_23706 : CollatzResearch.WordTrace tailWord_23706 prefixEnd_23706 7213376234423397846509 := by
  unfold tailWord_23706
  simp only [CollatzResearch.WordTrace]
  refine ⟨216157213031171376894743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 576419234749790338385981 216157213031171376894743)
  ·
    refine ⟨324235819546757065342115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216157213031171376894743 324235819546757065342115)
    ·
      refine ⟨486353729320135598013173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324235819546757065342115 486353729320135598013173)
      ·
        refine ⟨45595662123762712313735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 486353729320135598013173 45595662123762712313735)
        ·
          refine ⟨68393493185644068470603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45595662123762712313735 68393493185644068470603)
          ·
            refine ⟨102590239778466102705905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68393493185644068470603 102590239778466102705905)
            ·
              refine ⟨76942679833849577029429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102590239778466102705905 76942679833849577029429)
              ·
                refine ⟨7213376234423397846509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76942679833849577029429 7213376234423397846509)
                ·
                  rfl

theorem cell19_23706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_23706 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_23706 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_23706 prefixEnd_23706 := by exact prefixLift 23706
  have htrace : WordTrace (prefixWord ++ tailWord_23706) baseStart_23706 baseEnd_23706 := by
    simpa [prefixWord, tailWord_23706, baseEnd_23706] using wordTrace_append hprefix tailTrace_23706
  have hstable : (prefixWord ++ tailWord_23706).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23706).length < 2 ^ (prefixWord ++ tailWord_23706).sum := by decide
  have hdescent : baseEnd_23706 < baseStart_23706 := by decide
  rcases family_descends (prefixWord ++ tailWord_23706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23725 : List Nat := [1, 5, 2, 1, 3, 7]
def baseStart_23725 : Nat := 118140960795 + 23725 * 2 ^ 59
def prefixEnd_23725 : Nat := 4983230072969 + 3 ^ 40 * 23725 * 2
def baseEnd_23725 : Nat := 802128627359664824915

theorem tailTrace_23725 : CollatzResearch.WordTrace tailWord_23725 prefixEnd_23725 802128627359664824915 := by
  unfold tailWord_23725
  simp only [CollatzResearch.WordTrace]
  refine ⟨865321839055851752520629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 576881226037234501680419 865321839055851752520629)
  ·
    refine ⟨81123922411486101798809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 865321839055851752520629 81123922411486101798809)
    ·
      refine ⟨60842941808614576349107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81123922411486101798809 60842941808614576349107)
      ·
        refine ⟨91264412712921864523661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60842941808614576349107 91264412712921864523661)
        ·
          refine ⟨34224154767345699196373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91264412712921864523661 34224154767345699196373)
          ·
            refine ⟨802128627359664824915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 34224154767345699196373 802128627359664824915)
            ·
              rfl

theorem cell19_23725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 7].length) (baseStart_23725 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_23725 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_23725 prefixEnd_23725 := by exact prefixLift 23725
  have htrace : WordTrace (prefixWord ++ tailWord_23725) baseStart_23725 baseEnd_23725 := by
    simpa [prefixWord, tailWord_23725, baseEnd_23725] using wordTrace_append hprefix tailTrace_23725
  have hstable : (prefixWord ++ tailWord_23725).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23725).length < 2 ^ (prefixWord ++ tailWord_23725).sum := by decide
  have hdescent : baseEnd_23725 < baseStart_23725 := by decide
  rcases family_descends (prefixWord ++ tailWord_23725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23742 : List Nat := [4, 2, 1, 1, 3, 3, 1, 4]
def baseStart_23742 : Nat := 118140960795 + 23742 * 2 ^ 59
def prefixEnd_23742 : Nat := 4983230072969 + 3 ^ 40 * 23742 * 2
def baseEnd_23742 : Nat := 7224330488385981046411

theorem tailTrace_23742 : CollatzResearch.WordTrace tailWord_23742 prefixEnd_23742 7224330488385981046411 := by
  unfold tailWord_23742
  simp only [CollatzResearch.WordTrace]
  refine ⟨108242734999282956986185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 577294586662842437259653 108242734999282956986185)
  ·
    refine ⟨81182051249462217739639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108242734999282956986185 81182051249462217739639)
    ·
      refine ⟨121773076874193326609459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81182051249462217739639 121773076874193326609459)
      ·
        refine ⟨182659615311289989914189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121773076874193326609459 182659615311289989914189)
        ·
          refine ⟨68497355741733746217821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182659615311289989914189 68497355741733746217821)
          ·
            refine ⟨25686508403150154831683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68497355741733746217821 25686508403150154831683)
            ·
              refine ⟨38529762604725232247525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25686508403150154831683 38529762604725232247525)
              ·
                refine ⟨7224330488385981046411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38529762604725232247525 7224330488385981046411)
                ·
                  rfl

theorem cell19_23742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_23742 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_23742 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_23742 prefixEnd_23742 := by exact prefixLift 23742
  have htrace : WordTrace (prefixWord ++ tailWord_23742) baseStart_23742 baseEnd_23742 := by
    simpa [prefixWord, tailWord_23742, baseEnd_23742] using wordTrace_append hprefix tailTrace_23742
  have hstable : (prefixWord ++ tailWord_23742).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23742).length < 2 ^ (prefixWord ++ tailWord_23742).sum := by decide
  have hdescent : baseEnd_23742 < baseStart_23742 := by decide
  rcases family_descends (prefixWord ++ tailWord_23742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23757 : List Nat := [1, 6, 2, 2, 1, 1, 3, 3]
def baseStart_23757 : Nat := 118140960795 + 23757 * 2 ^ 59
def prefixEnd_23757 : Nat := 4983230072969 + 3 ^ 40 * 23757 * 2
def baseEnd_23757 : Nat := 7228894760870390713037

theorem tailTrace_23757 : CollatzResearch.WordTrace tailWord_23757 prefixEnd_23757 7228894760870390713037 := by
  unfold tailWord_23757
  simp only [CollatzResearch.WordTrace]
  refine ⟨866488974939921217685525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 577659316626614145123683 866488974939921217685525)
  ·
    refine ⟨40616670700308807079009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 866488974939921217685525 40616670700308807079009)
    ·
      refine ⟨30462503025231605309257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40616670700308807079009 30462503025231605309257)
      ·
        refine ⟨22846877268923703981943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30462503025231605309257 22846877268923703981943)
        ·
          refine ⟨34270315903385555972915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22846877268923703981943 34270315903385555972915)
          ·
            refine ⟨51405473855078333959373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34270315903385555972915 51405473855078333959373)
            ·
              refine ⟨19277052695654375234765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51405473855078333959373 19277052695654375234765)
              ·
                refine ⟨7228894760870390713037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19277052695654375234765 7228894760870390713037)
                ·
                  rfl

theorem cell19_23757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 3].length) (baseStart_23757 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_23757 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_23757 prefixEnd_23757 := by exact prefixLift 23757
  have htrace : WordTrace (prefixWord ++ tailWord_23757) baseStart_23757 baseEnd_23757 := by
    simpa [prefixWord, tailWord_23757, baseEnd_23757] using wordTrace_append hprefix tailTrace_23757
  have hstable : (prefixWord ++ tailWord_23757).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23757).length < 2 ^ (prefixWord ++ tailWord_23757).sum := by decide
  have hdescent : baseEnd_23757 < baseStart_23757 := by decide
  rcases family_descends (prefixWord ++ tailWord_23757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23784 : List Nat := [2, 1, 4, 1, 2, 1, 8]
def baseStart_23784 : Nat := 118140960795 + 23784 * 2 ^ 59
def prefixEnd_23784 : Nat := 4983230072969 + 3 ^ 40 * 23784 * 2
def baseEnd_23784 : Nat := 2412370150447442704321

theorem tailTrace_23784 : CollatzResearch.WordTrace tailWord_23784 prefixEnd_23784 2412370150447442704321 := by
  unfold tailWord_23784
  simp only [CollatzResearch.WordTrace]
  refine ⟨433736872921052414459203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 578315830561403219278937 433736872921052414459203)
  ·
    refine ⟨650605309381578621688805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 433736872921052414459203 650605309381578621688805)
    ·
      refine ⟨121988495509045991566651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 650605309381578621688805 121988495509045991566651)
      ·
        refine ⟨182982743263568987349977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121988495509045991566651 182982743263568987349977)
        ·
          refine ⟨137237057447676740512483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182982743263568987349977 137237057447676740512483)
          ·
            refine ⟨205855586171515110768725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137237057447676740512483 205855586171515110768725)
            ·
              refine ⟨2412370150447442704321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 205855586171515110768725 2412370150447442704321)
              ·
                rfl

theorem cell19_23784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 8].length) (baseStart_23784 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_23784 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_23784 prefixEnd_23784 := by exact prefixLift 23784
  have htrace : WordTrace (prefixWord ++ tailWord_23784) baseStart_23784 baseEnd_23784 := by
    simpa [prefixWord, tailWord_23784, baseEnd_23784] using wordTrace_append hprefix tailTrace_23784
  have hstable : (prefixWord ++ tailWord_23784).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23784).length < 2 ^ (prefixWord ++ tailWord_23784).sum := by decide
  have hdescent : baseEnd_23784 < baseStart_23784 := by decide
  rcases family_descends (prefixWord ++ tailWord_23784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23816 : List Nat := [2, 1, 3, 2, 5, 1, 2, 3]
def baseStart_23816 : Nat := 118140960795 + 23816 * 2 ^ 59
def prefixEnd_23816 : Nat := 4983230072969 + 3 ^ 40 * 23816 * 2
def baseEnd_23816 : Nat := 7246847565975735401765

theorem tailTrace_23816 : CollatzResearch.WordTrace tailWord_23816 prefixEnd_23816 7246847565975735401765 := by
  unfold tailWord_23816
  simp only [CollatzResearch.WordTrace]
  refine ⟨434320440863087147041651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 579093921150782862722201 434320440863087147041651)
  ·
    refine ⟨651480661294630720562477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 434320440863087147041651 651480661294630720562477)
    ·
      refine ⟨244305247985486520210929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 651480661294630720562477 244305247985486520210929)
      ·
        refine ⟨183228935989114890158197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244305247985486520210929 183228935989114890158197)
        ·
          refine ⟨17177712748979520952331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 183228935989114890158197 17177712748979520952331)
          ·
            refine ⟨25766569123469281428497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17177712748979520952331 25766569123469281428497)
            ·
              refine ⟨19324926842601961071373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25766569123469281428497 19324926842601961071373)
              ·
                refine ⟨7246847565975735401765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19324926842601961071373 7246847565975735401765)
                ·
                  rfl

theorem cell19_23816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 3].length) (baseStart_23816 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_23816 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_23816 prefixEnd_23816 := by exact prefixLift 23816
  have htrace : WordTrace (prefixWord ++ tailWord_23816) baseStart_23816 baseEnd_23816 := by
    simpa [prefixWord, tailWord_23816, baseEnd_23816] using wordTrace_append hprefix tailTrace_23816
  have hstable : (prefixWord ++ tailWord_23816).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23816).length < 2 ^ (prefixWord ++ tailWord_23816).sum := by decide
  have hdescent : baseEnd_23816 < baseStart_23816 := by decide
  rcases family_descends (prefixWord ++ tailWord_23816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23820 : List Nat := [2, 2, 1, 2, 2, 3, 4, 3]
def baseStart_23820 : Nat := 118140960795 + 23820 * 2 ^ 59
def prefixEnd_23820 : Nat := 4983230072969 + 3 ^ 40 * 23820 * 2
def baseEnd_23820 : Nat := 7248064705304911312865

theorem tailTrace_23820 : CollatzResearch.WordTrace tailWord_23820 prefixEnd_23820 7248064705304911312865 := by
  unfold tailWord_23820
  simp only [CollatzResearch.WordTrace]
  refine ⟨434393386855841488614457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 579191182474455318152609 434393386855841488614457)
  ·
    refine ⟨325795040141881116460843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 434393386855841488614457 325795040141881116460843)
    ·
      refine ⟨488692560212821674691265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325795040141881116460843 488692560212821674691265)
      ·
        refine ⟨366519420159616256018449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 488692560212821674691265 366519420159616256018449)
        ·
          refine ⟨274889565119712192013837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 366519420159616256018449 274889565119712192013837)
          ·
            refine ⟨103083586919892072005189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 274889565119712192013837 103083586919892072005189)
            ·
              refine ⟨19328172547479763500973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103083586919892072005189 19328172547479763500973)
              ·
                refine ⟨7248064705304911312865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19328172547479763500973 7248064705304911312865)
                ·
                  rfl

theorem cell19_23820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 3].length) (baseStart_23820 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_23820 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_23820 prefixEnd_23820 := by exact prefixLift 23820
  have htrace : WordTrace (prefixWord ++ tailWord_23820) baseStart_23820 baseEnd_23820 := by
    simpa [prefixWord, tailWord_23820, baseEnd_23820] using wordTrace_append hprefix tailTrace_23820
  have hstable : (prefixWord ++ tailWord_23820).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23820).length < 2 ^ (prefixWord ++ tailWord_23820).sum := by decide
  have hdescent : baseEnd_23820 < baseStart_23820 := by decide
  rcases family_descends (prefixWord ++ tailWord_23820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23839 : List Nat := [1, 1, 2, 4, 4, 2, 5]
def baseStart_23839 : Nat := 118140960795 + 23839 * 2 ^ 59
def prefixEnd_23839 : Nat := 4983230072969 + 3 ^ 40 * 23839 * 2
def baseEnd_23839 : Nat := 2417948705706165630197

theorem tailTrace_23839 : CollatzResearch.WordTrace tailWord_23839 prefixEnd_23839 2417948705706165630197 := by
  unfold tailWord_23839
  simp only [CollatzResearch.WordTrace]
  refine ⟨869479760642849222170571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 579653173761899481447047 869479760642849222170571)
  ·
    refine ⟨1304219640964273833255857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 869479760642849222170571 1304219640964273833255857)
    ·
      refine ⟨978164730723205374941893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1304219640964273833255857 978164730723205374941893)
      ·
        refine ⟨183405887010601007801605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 978164730723205374941893 183405887010601007801605)
        ·
          refine ⟨34388603814487688962801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 183405887010601007801605 34388603814487688962801)
          ·
            refine ⟨25791452860865766722101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34388603814487688962801 25791452860865766722101)
            ·
              refine ⟨2417948705706165630197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25791452860865766722101 2417948705706165630197)
              ·
                rfl

theorem cell19_23839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 5].length) (baseStart_23839 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_23839 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_23839 prefixEnd_23839 := by exact prefixLift 23839
  have htrace : WordTrace (prefixWord ++ tailWord_23839) baseStart_23839 baseEnd_23839 := by
    simpa [prefixWord, tailWord_23839, baseEnd_23839] using wordTrace_append hprefix tailTrace_23839
  have hstable : (prefixWord ++ tailWord_23839).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23839).length < 2 ^ (prefixWord ++ tailWord_23839).sum := by decide
  have hdescent : baseEnd_23839 < baseStart_23839 := by decide
  rcases family_descends (prefixWord ++ tailWord_23839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23858 : List Nat := [3, 2, 1, 1, 4, 2, 2, 4]
def baseStart_23858 : Nat := 118140960795 + 23858 * 2 ^ 59
def prefixEnd_23858 : Nat := 4983230072969 + 3 ^ 40 * 23858 * 2
def baseEnd_23858 : Nat := 7259627528932082468317

theorem tailTrace_23858 : CollatzResearch.WordTrace tailWord_23858 prefixEnd_23858 7259627528932082468317 := by
  unfold tailWord_23858
  simp only [CollatzResearch.WordTrace]
  refine ⟨217543186893503866778057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 580115165049343644741485 217543186893503866778057)
  ·
    refine ⟨163157390170127900083543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217543186893503866778057 163157390170127900083543)
    ·
      refine ⟨244736085255191850125315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163157390170127900083543 244736085255191850125315)
      ·
        refine ⟨367104127882787775187973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244736085255191850125315 367104127882787775187973)
        ·
          refine ⟨68832023978022707847745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 367104127882787775187973 68832023978022707847745)
          ·
            refine ⟨51624017983517030885809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68832023978022707847745 51624017983517030885809)
            ·
              refine ⟨38718013487637773164357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51624017983517030885809 38718013487637773164357)
              ·
                refine ⟨7259627528932082468317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38718013487637773164357 7259627528932082468317)
                ·
                  rfl

theorem cell19_23858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_23858 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_23858 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_23858 prefixEnd_23858 := by exact prefixLift 23858
  have htrace : WordTrace (prefixWord ++ tailWord_23858) baseStart_23858 baseEnd_23858 := by
    simpa [prefixWord, tailWord_23858, baseEnd_23858] using wordTrace_append hprefix tailTrace_23858
  have hstable : (prefixWord ++ tailWord_23858).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23858).length < 2 ^ (prefixWord ++ tailWord_23858).sum := by decide
  have hdescent : baseEnd_23858 < baseStart_23858 := by decide
  rcases family_descends (prefixWord ++ tailWord_23858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23879 : List Nat := [1, 1, 4, 1, 2, 3, 2, 5]
def baseStart_23879 : Nat := 118140960795 + 23879 * 2 ^ 59
def prefixEnd_23879 : Nat := 4983230072969 + 3 ^ 40 * 23879 * 2
def baseEnd_23879 : Nat := 7266017510410256001593

theorem tailTrace_23879 : CollatzResearch.WordTrace tailWord_23879 prefixEnd_23879 7266017510410256001593 := by
  unfold tailWord_23879
  simp only [CollatzResearch.WordTrace]
  refine ⟨870938680497936053626691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 580625786998624035751127 870938680497936053626691)
  ·
    refine ⟨1306408020746904080440037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 870938680497936053626691 1306408020746904080440037)
    ·
      refine ⟨244951503890044515082507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1306408020746904080440037 244951503890044515082507)
      ·
        refine ⟨367427255835066772623761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244951503890044515082507 367427255835066772623761)
        ·
          refine ⟨275570441876300079467821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 367427255835066772623761 275570441876300079467821)
          ·
            refine ⟨103338915703612529800433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 275570441876300079467821 103338915703612529800433)
            ·
              refine ⟨77504186777709397350325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103338915703612529800433 77504186777709397350325)
              ·
                refine ⟨7266017510410256001593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77504186777709397350325 7266017510410256001593)
                ·
                  rfl

theorem cell19_23879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 5].length) (baseStart_23879 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_23879 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_23879 prefixEnd_23879 := by exact prefixLift 23879
  have htrace : WordTrace (prefixWord ++ tailWord_23879) baseStart_23879 baseEnd_23879 := by
    simpa [prefixWord, tailWord_23879, baseEnd_23879] using wordTrace_append hprefix tailTrace_23879
  have hstable : (prefixWord ++ tailWord_23879).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23879).length < 2 ^ (prefixWord ++ tailWord_23879).sum := by decide
  have hdescent : baseEnd_23879 < baseStart_23879 := by decide
  rcases family_descends (prefixWord ++ tailWord_23879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_23989 : List Nat := [1, 3, 3, 2, 2, 3, 2, 3]
def baseStart_23989 : Nat := 118140960795 + 23989 * 2 ^ 59
def prefixEnd_23989 : Nat := 4983230072969 + 3 ^ 40 * 23989 * 2
def baseEnd_23989 : Nat := 7299488841962593556849

theorem tailTrace_23989 : CollatzResearch.WordTrace tailWord_23989 prefixEnd_23989 7299488841962593556849 := by
  unfold tailWord_23989
  simp only [CollatzResearch.WordTrace]
  refine ⟨874950710099424840131021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 583300473399616560087347 874950710099424840131021)
  ·
    refine ⟨328106516287284315049133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 874950710099424840131021 328106516287284315049133)
    ·
      refine ⟨123039943607731618143425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 328106516287284315049133 123039943607731618143425)
      ·
        refine ⟨92279957705798713607569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123039943607731618143425 92279957705798713607569)
        ·
          refine ⟨69209968279349035205677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92279957705798713607569 69209968279349035205677)
          ·
            refine ⟨25953738104755888202129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69209968279349035205677 25953738104755888202129)
            ·
              refine ⟨19465303578566916151597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25953738104755888202129 19465303578566916151597)
              ·
                refine ⟨7299488841962593556849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19465303578566916151597 7299488841962593556849)
                ·
                  rfl

theorem cell19_23989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 3].length) (baseStart_23989 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_23989 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_23989 prefixEnd_23989 := by exact prefixLift 23989
  have htrace : WordTrace (prefixWord ++ tailWord_23989) baseStart_23989 baseEnd_23989 := by
    simpa [prefixWord, tailWord_23989, baseEnd_23989] using wordTrace_append hprefix tailTrace_23989
  have hstable : (prefixWord ++ tailWord_23989).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_23989).length < 2 ^ (prefixWord ++ tailWord_23989).sum := by decide
  have hdescent : baseEnd_23989 < baseStart_23989 := by decide
  rcases family_descends (prefixWord ++ tailWord_23989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24002 : List Nat := [3, 5, 2, 1, 2, 1, 5]
def baseStart_24002 : Nat := 118140960795 + 24002 * 2 ^ 59
def prefixEnd_24002 : Nat := 4983230072969 + 3 ^ 40 * 24002 * 2
def baseEnd_24002 : Nat := 2434481514927471755975

theorem tailTrace_24002 : CollatzResearch.WordTrace tailWord_24002 prefixEnd_24002 2434481514927471755975 := by
  unfold tailWord_24002
  simp only [CollatzResearch.WordTrace]
  refine ⟨218856214763082015088565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 583616572701552040236173 218856214763082015088565)
  ·
    refine ⟨20517770134038938914553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 218856214763082015088565 20517770134038938914553)
    ·
      refine ⟨15388327600529204185915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20517770134038938914553 15388327600529204185915)
      ·
        refine ⟨23082491400793806278873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15388327600529204185915 23082491400793806278873)
        ·
          refine ⟨17311868550595354709155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23082491400793806278873 17311868550595354709155)
          ·
            refine ⟨25967802825893032063733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17311868550595354709155 25967802825893032063733)
            ·
              refine ⟨2434481514927471755975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25967802825893032063733 2434481514927471755975)
              ·
                rfl

theorem cell19_24002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 5].length) (baseStart_24002 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_24002 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_24002 prefixEnd_24002 := by exact prefixLift 24002
  have htrace : WordTrace (prefixWord ++ tailWord_24002) baseStart_24002 baseEnd_24002 := by
    simpa [prefixWord, tailWord_24002, baseEnd_24002] using wordTrace_append hprefix tailTrace_24002
  have hstable : (prefixWord ++ tailWord_24002).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24002).length < 2 ^ (prefixWord ++ tailWord_24002).sum := by decide
  have hdescent : baseEnd_24002 < baseStart_24002 := by decide
  rcases family_descends (prefixWord ++ tailWord_24002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24012 : List Nat := [2, 2, 1, 4, 2, 1, 7]
def baseStart_24012 : Nat := 118140960795 + 24012 * 2 ^ 59
def prefixEnd_24012 : Nat := 4983230072969 + 3 ^ 40 * 24012 * 2
def baseEnd_24012 : Nat := 2435495797701785015225

theorem tailTrace_24012 : CollatzResearch.WordTrace tailWord_24012 prefixEnd_24012 2435495797701785015225 := by
  unfold tailWord_24012
  simp only [CollatzResearch.WordTrace]
  refine ⟨437894794508049884109145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 583859726010733178812193 437894794508049884109145)
  ·
    refine ⟨328421095881037413081859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 437894794508049884109145 328421095881037413081859)
    ·
      refine ⟨492631643821556119622789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328421095881037413081859 492631643821556119622789)
      ·
        refine ⟨92368433216541772429273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 492631643821556119622789 92368433216541772429273)
        ·
          refine ⟨69276324912406329321955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92368433216541772429273 69276324912406329321955)
          ·
            refine ⟨103914487368609493982933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69276324912406329321955 103914487368609493982933)
            ·
              refine ⟨2435495797701785015225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 103914487368609493982933 2435495797701785015225)
              ·
                rfl

theorem cell19_24012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 7].length) (baseStart_24012 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_24012 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_24012 prefixEnd_24012 := by exact prefixLift 24012
  have htrace : WordTrace (prefixWord ++ tailWord_24012) baseStart_24012 baseEnd_24012 := by
    simpa [prefixWord, tailWord_24012, baseEnd_24012] using wordTrace_append hprefix tailTrace_24012
  have hstable : (prefixWord ++ tailWord_24012).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24012).length < 2 ^ (prefixWord ++ tailWord_24012).sum := by decide
  have hdescent : baseEnd_24012 < baseStart_24012 := by decide
  rcases family_descends (prefixWord ++ tailWord_24012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24029 : List Nat := [1, 4, 3, 1, 1, 3, 2, 4]
def baseStart_24029 : Nat := 118140960795 + 24029 * 2 ^ 59
def prefixEnd_24029 : Nat := 4983230072969 + 3 ^ 40 * 24029 * 2
def baseEnd_24029 : Nat := 7311660235254352667851

theorem tailTrace_24029 : CollatzResearch.WordTrace tailWord_24029 prefixEnd_24029 7311660235254352667851 := by
  unfold tailWord_24029
  simp only [CollatzResearch.WordTrace]
  refine ⟨876409629954511671587141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 584273086636341114391427 876409629954511671587141)
  ·
    refine ⟨164326805616470938422589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 876409629954511671587141 164326805616470938422589)
    ·
      refine ⟨61622552106176601908471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164326805616470938422589 61622552106176601908471)
      ·
        refine ⟨92433828159264902862707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61622552106176601908471 92433828159264902862707)
        ·
          refine ⟨138650742238897354294061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92433828159264902862707 138650742238897354294061)
          ·
            refine ⟨51994028339586507860273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138650742238897354294061 51994028339586507860273)
            ·
              refine ⟨38995521254689880895205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51994028339586507860273 38995521254689880895205)
              ·
                refine ⟨7311660235254352667851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38995521254689880895205 7311660235254352667851)
                ·
                  rfl

theorem cell19_24029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 4].length) (baseStart_24029 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_24029 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_24029 prefixEnd_24029 := by exact prefixLift 24029
  have htrace : WordTrace (prefixWord ++ tailWord_24029) baseStart_24029 baseEnd_24029 := by
    simpa [prefixWord, tailWord_24029, baseEnd_24029] using wordTrace_append hprefix tailTrace_24029
  have hstable : (prefixWord ++ tailWord_24029).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24029).length < 2 ^ (prefixWord ++ tailWord_24029).sum := by decide
  have hdescent : baseEnd_24029 < baseStart_24029 := by decide
  rcases family_descends (prefixWord ++ tailWord_24029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24031 : List Nat := [1, 1, 2, 3, 3, 1, 4, 4]
def baseStart_24031 : Nat := 118140960795 + 24031 * 2 ^ 59
def prefixEnd_24031 : Nat := 4983230072969 + 3 ^ 40 * 24031 * 2
def baseEnd_24031 : Nat := 7312268804918940623401

theorem tailTrace_24031 : CollatzResearch.WordTrace tailWord_24031 prefixEnd_24031 7312268804918940623401 := by
  unfold tailWord_24031
  simp only [CollatzResearch.WordTrace]
  refine ⟨876482575947266013159947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 584321717298177342106631 876482575947266013159947)
  ·
    refine ⟨1314723863920899019739921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 876482575947266013159947 1314723863920899019739921)
    ·
      refine ⟨986042897940674264804941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1314723863920899019739921 986042897940674264804941)
      ·
        refine ⟨369766086727752849301853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 986042897940674264804941 369766086727752849301853)
        ·
          refine ⟨138662282522907318488195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 369766086727752849301853 138662282522907318488195)
          ·
            refine ⟨207993423784360977732293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138662282522907318488195 207993423784360977732293)
            ·
              refine ⟨38998766959567683324805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 207993423784360977732293 38998766959567683324805)
              ·
                refine ⟨7312268804918940623401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38998766959567683324805 7312268804918940623401)
                ·
                  rfl

theorem cell19_24031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 4].length) (baseStart_24031 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_24031 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_24031 prefixEnd_24031 := by exact prefixLift 24031
  have htrace : WordTrace (prefixWord ++ tailWord_24031) baseStart_24031 baseEnd_24031 := by
    simpa [prefixWord, tailWord_24031, baseEnd_24031] using wordTrace_append hprefix tailTrace_24031
  have hstable : (prefixWord ++ tailWord_24031).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24031).length < 2 ^ (prefixWord ++ tailWord_24031).sum := by decide
  have hdescent : baseEnd_24031 < baseStart_24031 := by decide
  rcases family_descends (prefixWord ++ tailWord_24031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24164 : List Nat := [2, 3, 1, 1, 2, 4, 1, 5]
def baseStart_24164 : Nat := 118140960795 + 24164 * 2 ^ 59
def prefixEnd_24164 : Nat := 4983230072969 + 3 ^ 40 * 24164 * 2
def baseEnd_24164 : Nat := 7352738687614039667483

theorem tailTrace_24164 : CollatzResearch.WordTrace tailWord_24164 prefixEnd_24164 7352738687614039667483 := by
  unfold tailWord_24164
  simp only [CollatzResearch.WordTrace]
  refine ⟨440666742232714863875773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 587555656310286485167697 440666742232714863875773)
  ·
    refine ⟨165250028337268073953415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 440666742232714863875773 165250028337268073953415)
    ·
      refine ⟨247875042505902110930123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165250028337268073953415 247875042505902110930123)
      ·
        refine ⟨371812563758853166395185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247875042505902110930123 371812563758853166395185)
        ·
          refine ⟨278859422819139874796389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 371812563758853166395185 278859422819139874796389)
          ·
            refine ⟨52286141778588726524323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 278859422819139874796389 52286141778588726524323)
            ·
              refine ⟨78429212667883089786485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52286141778588726524323 78429212667883089786485)
              ·
                refine ⟨7352738687614039667483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78429212667883089786485 7352738687614039667483)
                ·
                  rfl

theorem cell19_24164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 5].length) (baseStart_24164 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_24164 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_24164 prefixEnd_24164 := by exact prefixLift 24164
  have htrace : WordTrace (prefixWord ++ tailWord_24164) baseStart_24164 baseEnd_24164 := by
    simpa [prefixWord, tailWord_24164, baseEnd_24164] using wordTrace_append hprefix tailTrace_24164
  have hstable : (prefixWord ++ tailWord_24164).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24164).length < 2 ^ (prefixWord ++ tailWord_24164).sum := by decide
  have hdescent : baseEnd_24164 < baseStart_24164 := by decide
  rcases family_descends (prefixWord ++ tailWord_24164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24181 : List Nat := [1, 3, 4, 2, 1, 3, 5]
def baseStart_24181 : Nat := 118140960795 + 24181 * 2 ^ 59
def prefixEnd_24181 : Nat := 4983230072969 + 3 ^ 40 * 24181 * 2
def baseEnd_24181 : Nat := 2452637176587679096553

theorem tailTrace_24181 : CollatzResearch.WordTrace tailWord_24181 prefixEnd_24181 2452637176587679096553 := by
  unfold tailWord_24181
  simp only [CollatzResearch.WordTrace]
  refine ⟨881953525403841631120397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 587969016935894420746931 881953525403841631120397)
  ·
    refine ⟨330732572026440611670149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 881953525403841631120397 330732572026440611670149)
    ·
      refine ⟨62012357254957614688153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 330732572026440611670149 62012357254957614688153)
      ·
        refine ⟨46509267941218211016115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62012357254957614688153 46509267941218211016115)
        ·
          refine ⟨69763901911827316524173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46509267941218211016115 69763901911827316524173)
          ·
            refine ⟨26161463216935243696565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69763901911827316524173 26161463216935243696565)
            ·
              refine ⟨2452637176587679096553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26161463216935243696565 2452637176587679096553)
              ·
                rfl

theorem cell19_24181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 5].length) (baseStart_24181 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_24181 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_24181 prefixEnd_24181 := by exact prefixLift 24181
  have htrace : WordTrace (prefixWord ++ tailWord_24181) baseStart_24181 baseEnd_24181 := by
    simpa [prefixWord, tailWord_24181, baseEnd_24181] using wordTrace_append hprefix tailTrace_24181
  have hstable : (prefixWord ++ tailWord_24181).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24181).length < 2 ^ (prefixWord ++ tailWord_24181).sum := by decide
  have hdescent : baseEnd_24181 < baseStart_24181 := by decide
  rcases family_descends (prefixWord ++ tailWord_24181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24202 : List Nat := [3, 1, 2, 3, 2, 1, 1, 6]
def baseStart_24202 : Nat := 118140960795 + 24202 * 2 ^ 59
def prefixEnd_24202 : Nat := 4983230072969 + 3 ^ 40 * 24202 * 2
def baseEnd_24202 : Nat := 7364301511241210822935

theorem tailTrace_24202 : CollatzResearch.WordTrace tailWord_24202 prefixEnd_24202 7364301511241210822935 := by
  unfold tailWord_24202
  simp only [CollatzResearch.WordTrace]
  refine ⟨220679864581940554408715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 588479638885174811756573 220679864581940554408715)
  ·
    refine ⟨331019796872910831613073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220679864581940554408715 331019796872910831613073)
    ·
      refine ⟨248264847654683123709805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 331019796872910831613073 248264847654683123709805)
      ·
        refine ⟨93099317870506171391177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 248264847654683123709805 93099317870506171391177)
        ·
          refine ⟨69824488402879628543383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93099317870506171391177 69824488402879628543383)
          ·
            refine ⟨104736732604319442815075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69824488402879628543383 104736732604319442815075)
            ·
              refine ⟨157105098906479164222613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104736732604319442815075 157105098906479164222613)
              ·
                refine ⟨7364301511241210822935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 157105098906479164222613 7364301511241210822935)
                ·
                  rfl

theorem cell19_24202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_24202 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_24202 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_24202 prefixEnd_24202 := by exact prefixLift 24202
  have htrace : WordTrace (prefixWord ++ tailWord_24202) baseStart_24202 baseEnd_24202 := by
    simpa [prefixWord, tailWord_24202, baseEnd_24202] using wordTrace_append hprefix tailTrace_24202
  have hstable : (prefixWord ++ tailWord_24202).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24202).length < 2 ^ (prefixWord ++ tailWord_24202).sum := by decide
  have hdescent : baseEnd_24202 < baseStart_24202 := by decide
  rcases family_descends (prefixWord ++ tailWord_24202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24238 : List Nat := [4, 1, 4, 1, 2, 7]
def baseStart_24238 : Nat := 118140960795 + 24238 * 2 ^ 59
def prefixEnd_24238 : Nat := 4983230072969 + 3 ^ 40 * 24238 * 2
def baseEnd_24238 : Nat := 819472862800421558093

theorem tailTrace_24238 : CollatzResearch.WordTrace tailWord_24238 prefixEnd_24238 819472862800421558093 := by
  unfold tailWord_24238
  simp only [CollatzResearch.WordTrace]
  refine ⟨110504060774667545743171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 589354990798226910630245 110504060774667545743171)
  ·
    refine ⟨165756091162001318614757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110504060774667545743171 165756091162001318614757)
    ·
      refine ⟨31079267092875247240267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165756091162001318614757 31079267092875247240267)
      ·
        refine ⟨46618900639312870860401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31079267092875247240267 46618900639312870860401)
        ·
          refine ⟨34964175479484653145301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46618900639312870860401 34964175479484653145301)
          ·
            refine ⟨819472862800421558093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 34964175479484653145301 819472862800421558093)
            ·
              rfl

theorem cell19_24238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 7].length) (baseStart_24238 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_24238 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_24238 prefixEnd_24238 := by exact prefixLift 24238
  have htrace : WordTrace (prefixWord ++ tailWord_24238) baseStart_24238 baseEnd_24238 := by
    simpa [prefixWord, tailWord_24238, baseEnd_24238] using wordTrace_append hprefix tailTrace_24238
  have hstable : (prefixWord ++ tailWord_24238).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24238).length < 2 ^ (prefixWord ++ tailWord_24238).sum := by decide
  have hdescent : baseEnd_24238 < baseStart_24238 := by decide
  rcases family_descends (prefixWord ++ tailWord_24238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24295 : List Nat := [1, 1, 5, 4, 1, 1, 6]
def baseStart_24295 : Nat := 118140960795 + 24295 * 2 ^ 59
def prefixEnd_24295 : Nat := 4983230072969 + 3 ^ 40 * 24295 * 2
def baseEnd_24295 : Nat := 2464200000214850252005

theorem tailTrace_24295 : CollatzResearch.WordTrace tailWord_24295 prefixEnd_24295 2464200000214850252005 := by
  unfold tailWord_24295
  simp only [CollatzResearch.WordTrace]
  refine ⟨886111446990839100770339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 590740964660559400513559 886111446990839100770339)
  ·
    refine ⟨1329167170486258651155509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 886111446990839100770339 1329167170486258651155509)
    ·
      refine ⟨124609422233086748545829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1329167170486258651155509 124609422233086748545829)
      ·
        refine ⟨23364266668703765352343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124609422233086748545829 23364266668703765352343)
        ·
          refine ⟨35046400003055648028515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23364266668703765352343 35046400003055648028515)
          ·
            refine ⟨52569600004583472042773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35046400003055648028515 52569600004583472042773)
            ·
              refine ⟨2464200000214850252005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 52569600004583472042773 2464200000214850252005)
              ·
                rfl

theorem cell19_24295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 6].length) (baseStart_24295 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_24295 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_24295 prefixEnd_24295 := by exact prefixLift 24295
  have htrace : WordTrace (prefixWord ++ tailWord_24295) baseStart_24295 baseEnd_24295 := by
    simpa [prefixWord, tailWord_24295, baseEnd_24295] using wordTrace_append hprefix tailTrace_24295
  have hstable : (prefixWord ++ tailWord_24295).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24295).length < 2 ^ (prefixWord ++ tailWord_24295).sum := by decide
  have hdescent : baseEnd_24295 < baseStart_24295 := by decide
  rcases family_descends (prefixWord ++ tailWord_24295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24394 : List Nat := [3, 1, 2, 1, 1, 1, 3, 7]
def baseStart_24394 : Nat := 118140960795 + 24394 * 2 ^ 59
def prefixEnd_24394 : Nat := 4983230072969 + 3 ^ 40 * 24394 * 2
def baseEnd_24394 : Nat := 7422724199041654555745

theorem tailTrace_24394 : CollatzResearch.WordTrace tailWord_24394 prefixEnd_24394 7422724199041654555745 := by
  unfold tailWord_24394
  simp only [CollatzResearch.WordTrace]
  refine ⟨222430568408044752156059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 593148182421452672416157 222430568408044752156059)
  ·
    refine ⟨333645852612067128234089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222430568408044752156059 333645852612067128234089)
    ·
      refine ⟨250234389459050346175567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333645852612067128234089 250234389459050346175567)
      ·
        refine ⟨375351584188575519263351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250234389459050346175567 375351584188575519263351)
        ·
          refine ⟨563027376282863278895027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375351584188575519263351 563027376282863278895027)
          ·
            refine ⟨844541064424294918342541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 563027376282863278895027 844541064424294918342541)
            ·
              refine ⟨316702899159110594378453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 844541064424294918342541 316702899159110594378453)
              ·
                refine ⟨7422724199041654555745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 316702899159110594378453 7422724199041654555745)
                ·
                  rfl

theorem cell19_24394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_24394 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_24394 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_24394 prefixEnd_24394 := by exact prefixLift 24394
  have htrace : WordTrace (prefixWord ++ tailWord_24394) baseStart_24394 baseEnd_24394 := by
    simpa [prefixWord, tailWord_24394, baseEnd_24394] using wordTrace_append hprefix tailTrace_24394
  have hstable : (prefixWord ++ tailWord_24394).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24394).length < 2 ^ (prefixWord ++ tailWord_24394).sum := by decide
  have hdescent : baseEnd_24394 < baseStart_24394 := by decide
  rcases family_descends (prefixWord ++ tailWord_24394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24426 : List Nat := [3, 1, 3, 4, 1, 2, 1, 4]
def baseStart_24426 : Nat := 118140960795 + 24426 * 2 ^ 59
def prefixEnd_24426 : Nat := 4983230072969 + 3 ^ 40 * 24426 * 2
def baseEnd_24426 : Nat := 7432461313675061844547

theorem tailTrace_24426 : CollatzResearch.WordTrace tailWord_24426 prefixEnd_24426 7432461313675061844547 := by
  unfold tailWord_24426
  simp only [CollatzResearch.WordTrace]
  refine ⟨222722352379062118447283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 593926273010832315859421 222722352379062118447283)
  ·
    refine ⟨334083528568593177670925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222722352379062118447283 334083528568593177670925)
    ·
      refine ⟨125281323213222441626597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 334083528568593177670925 125281323213222441626597)
      ·
        refine ⟨23490248102479207804987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125281323213222441626597 23490248102479207804987)
        ·
          refine ⟨35235372153718811707481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23490248102479207804987 35235372153718811707481)
          ·
            refine ⟨26426529115289108780611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35235372153718811707481 26426529115289108780611)
            ·
              refine ⟨39639793672933663170917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26426529115289108780611 39639793672933663170917)
              ·
                refine ⟨7432461313675061844547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39639793672933663170917 7432461313675061844547)
                ·
                  rfl

theorem cell19_24426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 4].length) (baseStart_24426 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_24426 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_24426 prefixEnd_24426 := by exact prefixLift 24426
  have htrace : WordTrace (prefixWord ++ tailWord_24426) baseStart_24426 baseEnd_24426 := by
    simpa [prefixWord, tailWord_24426, baseEnd_24426] using wordTrace_append hprefix tailTrace_24426
  have hstable : (prefixWord ++ tailWord_24426).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24426).length < 2 ^ (prefixWord ++ tailWord_24426).sum := by decide
  have hdescent : baseEnd_24426 < baseStart_24426 := by decide
  rcases family_descends (prefixWord ++ tailWord_24426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24468 : List Nat := [2, 4, 2, 1, 1, 3, 6]
def baseStart_24468 : Nat := 118140960795 + 24468 * 2 ^ 59
def prefixEnd_24468 : Nat := 4983230072969 + 3 ^ 40 * 24468 * 2
def baseEnd_24468 : Nat := 2481747092210469637033

theorem tailTrace_24468 : CollatzResearch.WordTrace tailWord_24468 prefixEnd_24468 2481747092210469637033 := by
  unfold tailWord_24468
  simp only [CollatzResearch.WordTrace]
  refine ⟨446210637682044823409029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 594947516909393097878705 446210637682044823409029)
  ·
    refine ⟨83664494565383404389193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 446210637682044823409029 83664494565383404389193)
    ·
      refine ⟨62748370924037553291895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83664494565383404389193 62748370924037553291895)
      ·
        refine ⟨94122556386056329937843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62748370924037553291895 94122556386056329937843)
        ·
          refine ⟨141183834579084494906765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94122556386056329937843 141183834579084494906765)
          ·
            refine ⟨52943937967156685590037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141183834579084494906765 52943937967156685590037)
            ·
              refine ⟨2481747092210469637033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 52943937967156685590037 2481747092210469637033)
              ·
                rfl

theorem cell19_24468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 6].length) (baseStart_24468 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_24468 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_24468 prefixEnd_24468 := by exact prefixLift 24468
  have htrace : WordTrace (prefixWord ++ tailWord_24468) baseStart_24468 baseEnd_24468 := by
    simpa [prefixWord, tailWord_24468, baseEnd_24468] using wordTrace_append hprefix tailTrace_24468
  have hstable : (prefixWord ++ tailWord_24468).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24468).length < 2 ^ (prefixWord ++ tailWord_24468).sum := by decide
  have hdescent : baseEnd_24468 < baseStart_24468 := by decide
  rcases family_descends (prefixWord ++ tailWord_24468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24500 : List Nat := [2, 5, 2, 1, 2, 2, 2, 3]
def baseStart_24500 : Nat := 118140960795 + 24500 * 2 ^ 59
def prefixEnd_24500 : Nat := 4983230072969 + 3 ^ 40 * 24500 * 2
def baseEnd_24500 : Nat := 7454978391264816199901

theorem tailTrace_24500 : CollatzResearch.WordTrace tailWord_24500 prefixEnd_24500 7454978391264816199901 := by
  unfold tailWord_24500
  simp only [CollatzResearch.WordTrace]
  refine ⟨446794205624079555991477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 595725607498772741321969 446794205624079555991477)
  ·
    refine ⟨41886956777257458374201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 446794205624079555991477 41886956777257458374201)
    ·
      refine ⟨31415217582943093780651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41886956777257458374201 31415217582943093780651)
      ·
        refine ⟨47122826374414640670977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31415217582943093780651 47122826374414640670977)
        ·
          refine ⟨35342119780810980503233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47122826374414640670977 35342119780810980503233)
          ·
            refine ⟨26506589835608235377425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35342119780810980503233 26506589835608235377425)
            ·
              refine ⟨19879942376706176533069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26506589835608235377425 19879942376706176533069)
              ·
                refine ⟨7454978391264816199901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19879942376706176533069 7454978391264816199901)
                ·
                  rfl

theorem cell19_24500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 3].length) (baseStart_24500 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_24500 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_24500 prefixEnd_24500 := by exact prefixLift 24500
  have htrace : WordTrace (prefixWord ++ tailWord_24500) baseStart_24500 baseEnd_24500 := by
    simpa [prefixWord, tailWord_24500, baseEnd_24500] using wordTrace_append hprefix tailTrace_24500
  have hstable : (prefixWord ++ tailWord_24500).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24500).length < 2 ^ (prefixWord ++ tailWord_24500).sum := by decide
  have hdescent : baseEnd_24500 < baseStart_24500 := by decide
  rcases family_descends (prefixWord ++ tailWord_24500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24580 : List Nat := [2, 3, 2, 4, 2, 6]
def baseStart_24580 : Nat := 118140960795 + 24580 * 2 ^ 59
def prefixEnd_24580 : Nat := 4983230072969 + 3 ^ 40 * 24580 * 2
def baseEnd_24580 : Nat := 831035686427592713545

theorem tailTrace_24580 : CollatzResearch.WordTrace tailWord_24580 prefixEnd_24580 831035686427592713545 := by
  unfold tailWord_24580
  simp only [CollatzResearch.WordTrace]
  refine ⟨448253125479166387447597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 597670833972221849930129 448253125479166387447597)
  ·
    refine ⟨168094922054687395292849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 448253125479166387447597 168094922054687395292849)
    ·
      refine ⟨126071191541015546469637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168094922054687395292849 126071191541015546469637)
      ·
        refine ⟨23638348413940414963057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126071191541015546469637 23638348413940414963057)
        ·
          refine ⟨17728761310455311222293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23638348413940414963057 17728761310455311222293)
          ·
            refine ⟨831035686427592713545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17728761310455311222293 831035686427592713545)
            ·
              rfl

theorem cell19_24580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 6].length) (baseStart_24580 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_24580 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_24580 prefixEnd_24580 := by exact prefixLift 24580
  have htrace : WordTrace (prefixWord ++ tailWord_24580) baseStart_24580 baseEnd_24580 := by
    simpa [prefixWord, tailWord_24580, baseEnd_24580] using wordTrace_append hprefix tailTrace_24580
  have hstable : (prefixWord ++ tailWord_24580).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24580).length < 2 ^ (prefixWord ++ tailWord_24580).sum := by decide
  have hdescent : baseEnd_24580 < baseStart_24580 := by decide
  rcases family_descends (prefixWord ++ tailWord_24580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24599 : List Nat := [1, 1, 3, 5, 2, 2, 1, 4]
def baseStart_24599 : Nat := 118140960795 + 24599 * 2 ^ 59
def prefixEnd_24599 : Nat := 4983230072969 + 3 ^ 40 * 24599 * 2
def baseEnd_24599 : Nat := 7485102589661919999631

theorem tailTrace_24599 : CollatzResearch.WordTrace tailWord_24599 prefixEnd_24599 7485102589661919999631 := by
  unfold tailWord_24599
  simp only [CollatzResearch.WordTrace]
  refine ⟨897199237889499019836851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 598132825259666013224567 897199237889499019836851)
  ·
    refine ⟨1345798856834248529755277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 897199237889499019836851 1345798856834248529755277)
    ·
      refine ⟨504674571312843198658229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1345798856834248529755277 504674571312843198658229)
      ·
        refine ⟨47313241060579049874209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 504674571312843198658229 47313241060579049874209)
        ·
          refine ⟨35484930795434287405657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47313241060579049874209 35484930795434287405657)
          ·
            refine ⟨26613698096575715554243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35484930795434287405657 26613698096575715554243)
            ·
              refine ⟨39920547144863573331365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26613698096575715554243 39920547144863573331365)
              ·
                refine ⟨7485102589661919999631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39920547144863573331365 7485102589661919999631)
                ·
                  rfl

theorem cell19_24599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 4].length) (baseStart_24599 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_24599 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_24599 prefixEnd_24599 := by exact prefixLift 24599
  have htrace : WordTrace (prefixWord ++ tailWord_24599) baseStart_24599 baseEnd_24599 := by
    simpa [prefixWord, tailWord_24599, baseEnd_24599] using wordTrace_append hprefix tailTrace_24599
  have hstable : (prefixWord ++ tailWord_24599).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24599).length < 2 ^ (prefixWord ++ tailWord_24599).sum := by decide
  have hdescent : baseEnd_24599 < baseStart_24599 := by decide
  rcases family_descends (prefixWord ++ tailWord_24599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24616 : List Nat := [2, 1, 5, 3, 1, 1, 3, 3]
def baseStart_24616 : Nat := 118140960795 + 24616 * 2 ^ 59
def prefixEnd_24616 : Nat := 4983230072969 + 3 ^ 40 * 24616 * 2
def baseEnd_24616 : Nat := 7490275431810917621807

theorem tailTrace_24616 : CollatzResearch.WordTrace tailWord_24616 prefixEnd_24616 7490275431810917621807 := by
  unfold tailWord_24616
  simp only [CollatzResearch.WordTrace]
  refine ⟨448909639413955461602851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 598546185885273948803801 448909639413955461602851)
  ·
    refine ⟨673364459120933192404277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 448909639413955461602851 673364459120933192404277)
    ·
      refine ⟨63127918042587486787901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 673364459120933192404277 63127918042587486787901)
      ·
        refine ⟨23672969265970307545463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63127918042587486787901 23672969265970307545463)
        ·
          refine ⟨35509453898955461318195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23672969265970307545463 35509453898955461318195)
          ·
            refine ⟨53264180848433191977293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35509453898955461318195 53264180848433191977293)
            ·
              refine ⟨19974067818162446991485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53264180848433191977293 19974067818162446991485)
              ·
                refine ⟨7490275431810917621807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19974067818162446991485 7490275431810917621807)
                ·
                  rfl

theorem cell19_24616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 3].length) (baseStart_24616 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_24616 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_24616 prefixEnd_24616 := by exact prefixLift 24616
  have htrace : WordTrace (prefixWord ++ tailWord_24616) baseStart_24616 baseEnd_24616 := by
    simpa [prefixWord, tailWord_24616, baseEnd_24616] using wordTrace_append hprefix tailTrace_24616
  have hstable : (prefixWord ++ tailWord_24616).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24616).length < 2 ^ (prefixWord ++ tailWord_24616).sum := by decide
  have hdescent : baseEnd_24616 < baseStart_24616 := by decide
  rcases family_descends (prefixWord ++ tailWord_24616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24618 : List Nat := [3, 1, 4, 1, 2, 2, 3, 3]
def baseStart_24618 : Nat := 118140960795 + 24618 * 2 ^ 59
def prefixEnd_24618 : Nat := 4983230072969 + 3 ^ 40 * 24618 * 2
def baseEnd_24618 : Nat := 7490884001475505577357

theorem tailTrace_24618 : CollatzResearch.WordTrace tailWord_24618 prefixEnd_24618 7490884001475505577357 := by
  unfold tailWord_24618
  simp only [CollatzResearch.WordTrace]
  refine ⟨224473056205166316194627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 598594816547110176519005 224473056205166316194627)
  ·
    refine ⟨336709584307749474291941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224473056205166316194627 336709584307749474291941)
    ·
      refine ⟨63133047057703026429739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 336709584307749474291941 63133047057703026429739)
      ·
        refine ⟨94699570586554539644609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63133047057703026429739 94699570586554539644609)
        ·
          refine ⟨71024677939915904733457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94699570586554539644609 71024677939915904733457)
          ·
            refine ⟨53268508454936928550093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71024677939915904733457 53268508454936928550093)
            ·
              refine ⟨19975690670601348206285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53268508454936928550093 19975690670601348206285)
              ·
                refine ⟨7490884001475505577357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19975690670601348206285 7490884001475505577357)
                ·
                  rfl

theorem cell19_24618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 3].length) (baseStart_24618 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_24618 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_24618 prefixEnd_24618 := by exact prefixLift 24618
  have htrace : WordTrace (prefixWord ++ tailWord_24618) baseStart_24618 baseEnd_24618 := by
    simpa [prefixWord, tailWord_24618, baseEnd_24618] using wordTrace_append hprefix tailTrace_24618
  have hstable : (prefixWord ++ tailWord_24618).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24618).length < 2 ^ (prefixWord ++ tailWord_24618).sum := by decide
  have hdescent : baseEnd_24618 < baseStart_24618 := by decide
  rcases family_descends (prefixWord ++ tailWord_24618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24660 : List Nat := [2, 4, 1, 1, 1, 1, 1, 8]
def baseStart_24660 : Nat := 118140960795 + 24660 * 2 ^ 59
def prefixEnd_24660 : Nat := 4983230072969 + 3 ^ 40 * 24660 * 2
def baseEnd_24660 : Nat := 7503663964431852643909

theorem tailTrace_24660 : CollatzResearch.WordTrace tailWord_24660 prefixEnd_24660 7503663964431852643909 := by
  unfold tailWord_24660
  simp only [CollatzResearch.WordTrace]
  refine ⟨449712045334253218903717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 599616060445670958538289 449712045334253218903717)
  ·
    refine ⟨84321008500172478544447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 449712045334253218903717 84321008500172478544447)
    ·
      refine ⟨126481512750258717816671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84321008500172478544447 126481512750258717816671)
      ·
        refine ⟨189722269125388076725007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126481512750258717816671 189722269125388076725007)
        ·
          refine ⟨284583403688082115087511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189722269125388076725007 284583403688082115087511)
          ·
            refine ⟨426875105532123172631267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284583403688082115087511 426875105532123172631267)
            ·
              refine ⟨640312658298184758946901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 426875105532123172631267 640312658298184758946901)
              ·
                refine ⟨7503663964431852643909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 640312658298184758946901 7503663964431852643909)
                ·
                  rfl

theorem cell19_24660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 8].length) (baseStart_24660 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_24660 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_24660 prefixEnd_24660 := by exact prefixLift 24660
  have htrace : WordTrace (prefixWord ++ tailWord_24660) baseStart_24660 baseEnd_24660 := by
    simpa [prefixWord, tailWord_24660, baseEnd_24660] using wordTrace_append hprefix tailTrace_24660
  have hstable : (prefixWord ++ tailWord_24660).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24660).length < 2 ^ (prefixWord ++ tailWord_24660).sum := by decide
  have hdescent : baseEnd_24660 < baseStart_24660 := by decide
  rcases family_descends (prefixWord ++ tailWord_24660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24677 : List Nat := [1, 3, 1, 3, 2, 2, 4, 3]
def baseStart_24677 : Nat := 118140960795 + 24677 * 2 ^ 59
def prefixEnd_24677 : Nat := 4983230072969 + 3 ^ 40 * 24677 * 2
def baseEnd_24677 : Nat := 7508836806580850266085

theorem tailTrace_24677 : CollatzResearch.WordTrace tailWord_24677 prefixEnd_24677 7508836806580850266085 := by
  unfold tailWord_24677
  simp only [CollatzResearch.WordTrace]
  refine ⟨900044131606918341176285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 600029421071278894117523 900044131606918341176285)
  ·
    refine ⟨337516549352594377941107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 900044131606918341176285 337516549352594377941107)
    ·
      refine ⟨506274824028891566911661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337516549352594377941107 506274824028891566911661)
      ·
        refine ⟨189853059010834337591873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 506274824028891566911661 189853059010834337591873)
        ·
          refine ⟨142389794258125753193905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189853059010834337591873 142389794258125753193905)
          ·
            refine ⟨106792345693594314895429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142389794258125753193905 106792345693594314895429)
            ·
              refine ⟨20023564817548934042893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106792345693594314895429 20023564817548934042893)
              ·
                refine ⟨7508836806580850266085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20023564817548934042893 7508836806580850266085)
                ·
                  rfl

theorem cell19_24677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 3].length) (baseStart_24677 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_24677 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_24677 prefixEnd_24677 := by exact prefixLift 24677
  have htrace : WordTrace (prefixWord ++ tailWord_24677) baseStart_24677 baseEnd_24677 := by
    simpa [prefixWord, tailWord_24677, baseEnd_24677] using wordTrace_append hprefix tailTrace_24677
  have hstable : (prefixWord ++ tailWord_24677).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24677).length < 2 ^ (prefixWord ++ tailWord_24677).sum := by decide
  have hdescent : baseEnd_24677 < baseStart_24677 := by decide
  rcases family_descends (prefixWord ++ tailWord_24677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24679 : List Nat := [1, 1, 5, 1, 1, 2, 3, 5]
def baseStart_24679 : Nat := 118140960795 + 24679 * 2 ^ 59
def prefixEnd_24679 : Nat := 4983230072969 + 3 ^ 40 * 24679 * 2
def baseEnd_24679 : Nat := 7509445376245438221635

theorem tailTrace_24679 : CollatzResearch.WordTrace tailWord_24679 prefixEnd_24679 7509445376245438221635 := by
  unfold tailWord_24679
  simp only [CollatzResearch.WordTrace]
  refine ⟨900117077599672682749091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 600078051733115121832727 900117077599672682749091)
  ·
    refine ⟨1350175616399509024123637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 900117077599672682749091 1350175616399509024123637)
    ·
      refine ⟨126578964037453971011591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1350175616399509024123637 126578964037453971011591)
      ·
        refine ⟨189868446056180956517387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126578964037453971011591 189868446056180956517387)
        ·
          refine ⟨284802669084271434776081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189868446056180956517387 284802669084271434776081)
          ·
            refine ⟨213602001813203576082061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 284802669084271434776081 213602001813203576082061)
            ·
              refine ⟨80100750679951341030773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 213602001813203576082061 80100750679951341030773)
              ·
                refine ⟨7509445376245438221635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80100750679951341030773 7509445376245438221635)
                ·
                  rfl

theorem cell19_24679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 5].length) (baseStart_24679 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_24679 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_24679 prefixEnd_24679 := by exact prefixLift 24679
  have htrace : WordTrace (prefixWord ++ tailWord_24679) baseStart_24679 baseEnd_24679 := by
    simpa [prefixWord, tailWord_24679, baseEnd_24679] using wordTrace_append hprefix tailTrace_24679
  have hstable : (prefixWord ++ tailWord_24679).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24679).length < 2 ^ (prefixWord ++ tailWord_24679).sum := by decide
  have hdescent : baseEnd_24679 < baseStart_24679 := by decide
  rcases family_descends (prefixWord ++ tailWord_24679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24736 : List Nat := [2, 1, 1, 4, 2, 2, 2, 5]
def baseStart_24736 : Nat := 118140960795 + 24736 * 2 ^ 59
def prefixEnd_24736 : Nat := 4983230072969 + 3 ^ 40 * 24736 * 2
def baseEnd_24736 : Nat := 7526789611686194954813

theorem tailTrace_24736 : CollatzResearch.WordTrace tailWord_24736 prefixEnd_24736 7526789611686194954813 := by
  unfold tailWord_24736
  simp only [CollatzResearch.WordTrace]
  refine ⟨451098019196585708787031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 601464025595447611716041 451098019196585708787031)
  ·
    refine ⟨676647028794878563180547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 451098019196585708787031 676647028794878563180547)
    ·
      refine ⟨1014970543192317844770821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 676647028794878563180547 1014970543192317844770821)
      ·
        refine ⟨190306976848559595894529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1014970543192317844770821 190306976848559595894529)
        ·
          refine ⟨142730232636419696920897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190306976848559595894529 142730232636419696920897)
          ·
            refine ⟨107047674477314772690673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142730232636419696920897 107047674477314772690673)
            ·
              refine ⟨80285755857986079518005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107047674477314772690673 80285755857986079518005)
              ·
                refine ⟨7526789611686194954813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80285755857986079518005 7526789611686194954813)
                ·
                  rfl

theorem cell19_24736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 5].length) (baseStart_24736 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_24736 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_24736 prefixEnd_24736 := by exact prefixLift 24736
  have htrace : WordTrace (prefixWord ++ tailWord_24736) baseStart_24736 baseEnd_24736 := by
    simpa [prefixWord, tailWord_24736, baseEnd_24736] using wordTrace_append hprefix tailTrace_24736
  have hstable : (prefixWord ++ tailWord_24736).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24736).length < 2 ^ (prefixWord ++ tailWord_24736).sum := by decide
  have hdescent : baseEnd_24736 < baseStart_24736 := by decide
  rcases family_descends (prefixWord ++ tailWord_24736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24753 : List Nat := [1, 2, 2, 5, 3, 6]
def baseStart_24753 : Nat := 118140960795 + 24753 * 2 ^ 59
def prefixEnd_24753 : Nat := 4983230072969 + 3 ^ 40 * 24753 * 2
def baseEnd_24753 : Nat := 836884717092799175221

theorem tailTrace_24753 : CollatzResearch.WordTrace tailWord_24753 prefixEnd_24753 836884717092799175221 := by
  unfold tailWord_24753
  simp only [CollatzResearch.WordTrace]
  refine ⟨902816079331583320942913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 601877386221055547295275 902816079331583320942913)
  ·
    refine ⟨677112059498687490707185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 902816079331583320942913 677112059498687490707185)
    ·
      refine ⟨507834044624015618030389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 677112059498687490707185 507834044624015618030389)
      ·
        refine ⟨47609441683501464190349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 507834044624015618030389 47609441683501464190349)
        ·
          refine ⟨17853540631313049071381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47609441683501464190349 17853540631313049071381)
          ·
            refine ⟨836884717092799175221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17853540631313049071381 836884717092799175221)
            ·
              rfl

theorem cell19_24753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 6].length) (baseStart_24753 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_24753 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_24753 prefixEnd_24753 := by exact prefixLift 24753
  have htrace : WordTrace (prefixWord ++ tailWord_24753) baseStart_24753 baseEnd_24753 := by
    simpa [prefixWord, tailWord_24753, baseEnd_24753] using wordTrace_append hprefix tailTrace_24753
  have hstable : (prefixWord ++ tailWord_24753).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24753).length < 2 ^ (prefixWord ++ tailWord_24753).sum := by decide
  have hdescent : baseEnd_24753 < baseStart_24753 := by decide
  rcases family_descends (prefixWord ++ tailWord_24753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24772 : List Nat := [2, 3, 3, 1, 2, 1, 3, 4]
def baseStart_24772 : Nat := 118140960795 + 24772 * 2 ^ 59
def prefixEnd_24772 : Nat := 4983230072969 + 3 ^ 40 * 24772 * 2
def baseEnd_24772 : Nat := 7537743865648778154715

theorem tailTrace_24772 : CollatzResearch.WordTrace tailWord_24772 prefixEnd_24772 7537743865648778154715 := by
  unfold tailWord_24772
  simp only [CollatzResearch.WordTrace]
  refine ⟨451754533131374782942285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 602339377508499710589713 451754533131374782942285)
  ·
    refine ⟨169407949924265543603357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 451754533131374782942285 169407949924265543603357)
    ·
      refine ⟨63527981221599578851259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169407949924265543603357 63527981221599578851259)
      ·
        refine ⟨95291971832399368276889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63527981221599578851259 95291971832399368276889)
        ·
          refine ⟨71468978874299526207667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95291971832399368276889 71468978874299526207667)
          ·
            refine ⟨107203468311449289311501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71468978874299526207667 107203468311449289311501)
            ·
              refine ⟨40201300616793483491813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107203468311449289311501 40201300616793483491813)
              ·
                refine ⟨7537743865648778154715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40201300616793483491813 7537743865648778154715)
                ·
                  rfl

theorem cell19_24772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 4].length) (baseStart_24772 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_24772 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_24772 prefixEnd_24772 := by exact prefixLift 24772
  have htrace : WordTrace (prefixWord ++ tailWord_24772) baseStart_24772 baseEnd_24772 := by
    simpa [prefixWord, tailWord_24772, baseEnd_24772] using wordTrace_append hprefix tailTrace_24772
  have hstable : (prefixWord ++ tailWord_24772).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24772).length < 2 ^ (prefixWord ++ tailWord_24772).sum := by decide
  have hdescent : baseEnd_24772 < baseStart_24772 := by decide
  rcases family_descends (prefixWord ++ tailWord_24772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24789 : List Nat := [1, 3, 2, 4, 2, 1, 3, 3]
def baseStart_24789 : Nat := 118140960795 + 24789 * 2 ^ 59
def prefixEnd_24789 : Nat := 4983230072969 + 3 ^ 40 * 24789 * 2
def baseEnd_24789 : Nat := 7542916707797775776891

theorem tailTrace_24789 : CollatzResearch.WordTrace tailWord_24789 prefixEnd_24789 7542916707797775776891 := by
  unfold tailWord_24789
  simp only [CollatzResearch.WordTrace]
  refine ⟨904129107201161469253421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 602752738134107646168947 904129107201161469253421)
  ·
    refine ⟨339048415200435550970033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 904129107201161469253421 339048415200435550970033)
    ·
      refine ⟨254286311400326663227525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339048415200435550970033 254286311400326663227525)
      ·
        refine ⟨47678683387561249355161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 254286311400326663227525 47678683387561249355161)
        ·
          refine ⟨35759012540670937016371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47678683387561249355161 35759012540670937016371)
          ·
            refine ⟨53638518811006405524557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35759012540670937016371 53638518811006405524557)
            ·
              refine ⟨20114444554127402071709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53638518811006405524557 20114444554127402071709)
              ·
                refine ⟨7542916707797775776891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20114444554127402071709 7542916707797775776891)
                ·
                  rfl

theorem cell19_24789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 3].length) (baseStart_24789 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_24789 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_24789 prefixEnd_24789 := by exact prefixLift 24789
  have htrace : WordTrace (prefixWord ++ tailWord_24789) baseStart_24789 baseEnd_24789 := by
    simpa [prefixWord, tailWord_24789, baseEnd_24789] using wordTrace_append hprefix tailTrace_24789
  have hstable : (prefixWord ++ tailWord_24789).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24789).length < 2 ^ (prefixWord ++ tailWord_24789).sum := by decide
  have hdescent : baseEnd_24789 < baseStart_24789 := by decide
  rcases family_descends (prefixWord ++ tailWord_24789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24924 : List Nat := [2, 2, 4, 3, 1, 7]
def baseStart_24924 : Nat := 118140960795 + 24924 * 2 ^ 59
def prefixEnd_24924 : Nat := 4983230072969 + 3 ^ 40 * 24924 * 2
def baseEnd_24924 : Nat := 842666128906384752947

theorem tailTrace_24924 : CollatzResearch.WordTrace tailWord_24924 prefixEnd_24924 842666128906384752947 := by
  unfold tailWord_24924
  simp only [CollatzResearch.WordTrace]
  refine ⟨454526480856039762708913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 606035307808053016945217 454526480856039762708913)
  ·
    refine ⟨340894860642029822031685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 454526480856039762708913 340894860642029822031685)
    ·
      refine ⟨63917786370380591630941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 340894860642029822031685 63917786370380591630941)
      ·
        refine ⟨23969169888892721861603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63917786370380591630941 23969169888892721861603)
        ·
          refine ⟨35953754833339082792405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23969169888892721861603 35953754833339082792405)
          ·
            refine ⟨842666128906384752947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 35953754833339082792405 842666128906384752947)
            ·
              rfl

theorem cell19_24924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 7].length) (baseStart_24924 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_24924 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_24924 prefixEnd_24924 := by exact prefixLift 24924
  have htrace : WordTrace (prefixWord ++ tailWord_24924) baseStart_24924 baseEnd_24924 := by
    simpa [prefixWord, tailWord_24924, baseEnd_24924] using wordTrace_append hprefix tailTrace_24924
  have hstable : (prefixWord ++ tailWord_24924).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24924).length < 2 ^ (prefixWord ++ tailWord_24924).sum := by decide
  have hdescent : baseEnd_24924 < baseStart_24924 := by decide
  rcases family_descends (prefixWord ++ tailWord_24924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24928 : List Nat := [2, 1, 1, 3, 12]
def baseStart_24928 : Nat := 118140960795 + 24928 * 2 ^ 59
def prefixEnd_24928 : Nat := 4983230072969 + 3 ^ 40 * 24928 * 2
def baseEnd_24928 : Nat := 280933788869875506949

theorem tailTrace_24928 : CollatzResearch.WordTrace tailWord_24928 prefixEnd_24928 280933788869875506949 := by
  unfold tailWord_24928
  simp only [CollatzResearch.WordTrace]
  refine ⟨454599426848794104281719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 606132569131725472375625 454599426848794104281719)
  ·
    refine ⟨681899140273191156422579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 454599426848794104281719 681899140273191156422579)
    ·
      refine ⟨1022848710409786734633869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 681899140273191156422579 1022848710409786734633869)
      ·
        refine ⟨383568266403670025487701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1022848710409786734633869 383568266403670025487701)
        ·
          refine ⟨280933788869875506949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 383568266403670025487701 280933788869875506949)
          ·
            rfl

theorem cell19_24928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 12].length) (baseStart_24928 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_24928 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_24928 prefixEnd_24928 := by exact prefixLift 24928
  have htrace : WordTrace (prefixWord ++ tailWord_24928) baseStart_24928 baseEnd_24928 := by
    simpa [prefixWord, tailWord_24928, baseEnd_24928] using wordTrace_append hprefix tailTrace_24928
  have hstable : (prefixWord ++ tailWord_24928).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24928).length < 2 ^ (prefixWord ++ tailWord_24928).sum := by decide
  have hdescent : baseEnd_24928 < baseStart_24928 := by decide
  rcases family_descends (prefixWord ++ tailWord_24928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_24985 : List Nat := [1, 2, 1, 2, 1, 4, 8]
def baseStart_24985 : Nat := 118140960795 + 24985 * 2 ^ 59
def prefixEnd_24985 : Nat := 4983230072969 + 3 ^ 40 * 24985 * 2
def baseEnd_24985 : Nat := 2534185511642465140267

theorem tailTrace_24985 : CollatzResearch.WordTrace tailWord_24985 prefixEnd_24985 2534185511642465140267 := by
  unfold tailWord_24985
  simp only [CollatzResearch.WordTrace]
  refine ⟨911277814491086943388409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 607518542994057962258939 911277814491086943388409)
  ·
    refine ⟨683458360868315207541307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 911277814491086943388409 683458360868315207541307)
    ·
      refine ⟨1025187541302472811311961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 683458360868315207541307 1025187541302472811311961)
      ·
        refine ⟨768890655976854608483971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1025187541302472811311961 768890655976854608483971)
        ·
          refine ⟨1153335983965281912725957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 768890655976854608483971 1153335983965281912725957)
          ·
            refine ⟨216250496993490358636117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1153335983965281912725957 216250496993490358636117)
            ·
              refine ⟨2534185511642465140267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 216250496993490358636117 2534185511642465140267)
              ·
                rfl

theorem cell19_24985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 8].length) (baseStart_24985 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_24985 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_24985 prefixEnd_24985 := by exact prefixLift 24985
  have htrace : WordTrace (prefixWord ++ tailWord_24985) baseStart_24985 baseEnd_24985 := by
    simpa [prefixWord, tailWord_24985, baseEnd_24985] using wordTrace_append hprefix tailTrace_24985
  have hstable : (prefixWord ++ tailWord_24985).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_24985).length < 2 ^ (prefixWord ++ tailWord_24985).sum := by decide
  have hdescent : baseEnd_24985 < baseStart_24985 := by decide
  rcases family_descends (prefixWord ++ tailWord_24985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25004 : List Nat := [2, 2, 1, 1, 1, 1, 3, 8]
def baseStart_25004 : Nat := 118140960795 + 25004 * 2 ^ 59
def prefixEnd_25004 : Nat := 4983230072969 + 3 ^ 40 * 25004 * 2
def baseEnd_25004 : Nat := 7608337946740980998527

theorem tailTrace_25004 : CollatzResearch.WordTrace tailWord_25004 prefixEnd_25004 7608337946740980998527 := by
  unfold tailWord_25004
  simp only [CollatzResearch.WordTrace]
  refine ⟨455985400711126594165033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 607980534281502125553377 455985400711126594165033)
  ·
    refine ⟨341989050533344945623775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 455985400711126594165033 341989050533344945623775)
    ·
      refine ⟨512983575800017418435663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341989050533344945623775 512983575800017418435663)
      ·
        refine ⟨769475363700026127653495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 512983575800017418435663 769475363700026127653495)
        ·
          refine ⟨1154213045550039191480243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 769475363700026127653495 1154213045550039191480243)
          ·
            refine ⟨1731319568325058787220365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1154213045550039191480243 1731319568325058787220365)
            ·
              refine ⟨649244838121897045207637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1731319568325058787220365 649244838121897045207637)
              ·
                refine ⟨7608337946740980998527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 649244838121897045207637 7608337946740980998527)
                ·
                  rfl

theorem cell19_25004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 8].length) (baseStart_25004 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_25004 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_25004 prefixEnd_25004 := by exact prefixLift 25004
  have htrace : WordTrace (prefixWord ++ tailWord_25004) baseStart_25004 baseEnd_25004 := by
    simpa [prefixWord, tailWord_25004, baseEnd_25004] using wordTrace_append hprefix tailTrace_25004
  have hstable : (prefixWord ++ tailWord_25004).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25004).length < 2 ^ (prefixWord ++ tailWord_25004).sum := by decide
  have hdescent : baseEnd_25004 < baseStart_25004 := by decide
  rcases family_descends (prefixWord ++ tailWord_25004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25021 : List Nat := [1, 4, 1, 2, 2, 3, 1, 5]
def baseStart_25021 : Nat := 118140960795 + 25021 * 2 ^ 59
def prefixEnd_25021 : Nat := 4983230072969 + 3 ^ 40 * 25021 * 2
def baseEnd_25021 : Nat := 7613510788889978620703

theorem tailTrace_25021 : CollatzResearch.WordTrace tailWord_25021 prefixEnd_25021 7613510788889978620703 := by
  unfold tailWord_25021
  simp only [CollatzResearch.WordTrace]
  refine ⟨912590842360665091698917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 608393894907110061132611 912590842360665091698917)
  ·
    refine ⟨171110782942624704693547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 912590842360665091698917 171110782942624704693547)
    ·
      refine ⟨256666174413937057040321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171110782942624704693547 256666174413937057040321)
      ·
        refine ⟨192499630810452792780241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256666174413937057040321 192499630810452792780241)
        ·
          refine ⟨144374723107839594585181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192499630810452792780241 144374723107839594585181)
          ·
            refine ⟨54140521165439847969443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144374723107839594585181 54140521165439847969443)
            ·
              refine ⟨81210781748159771954165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54140521165439847969443 81210781748159771954165)
              ·
                refine ⟨7613510788889978620703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81210781748159771954165 7613510788889978620703)
                ·
                  rfl

theorem cell19_25021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 5].length) (baseStart_25021 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_25021 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_25021 prefixEnd_25021 := by exact prefixLift 25021
  have htrace : WordTrace (prefixWord ++ tailWord_25021) baseStart_25021 baseEnd_25021 := by
    simpa [prefixWord, tailWord_25021, baseEnd_25021] using wordTrace_append hprefix tailTrace_25021
  have hstable : (prefixWord ++ tailWord_25021).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25021).length < 2 ^ (prefixWord ++ tailWord_25021).sum := by decide
  have hdescent : baseEnd_25021 < baseStart_25021 := by decide
  rcases family_descends (prefixWord ++ tailWord_25021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25078 : List Nat := [5, 1, 1, 1, 2, 1, 1, 7]
def baseStart_25078 : Nat := 118140960795 + 25078 * 2 ^ 59
def prefixEnd_25078 : Nat := 4983230072969 + 3 ^ 40 * 25078 * 2
def baseEnd_25078 : Nat := 7630855024330735353881

theorem tailTrace_25078 : CollatzResearch.WordTrace tailWord_25078 prefixEnd_25078 7630855024330735353881 := by
  unfold tailWord_25078
  simp only [CollatzResearch.WordTrace]
  refine ⟨57166862697135239157743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 609779868769442551015925 57166862697135239157743)
  ·
    refine ⟨85750294045702858736615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57166862697135239157743 85750294045702858736615)
    ·
      refine ⟨128625441068554288104923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85750294045702858736615 128625441068554288104923)
      ·
        refine ⟨192938161602831432157385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128625441068554288104923 192938161602831432157385)
        ·
          refine ⟨144703621202123574118039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192938161602831432157385 144703621202123574118039)
          ·
            refine ⟨217055431803185361177059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144703621202123574118039 217055431803185361177059)
            ·
              refine ⟨325583147704778041765589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217055431803185361177059 325583147704778041765589)
              ·
                refine ⟨7630855024330735353881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 325583147704778041765589 7630855024330735353881)
                ·
                  rfl

theorem cell19_25078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_25078 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_25078 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_25078 prefixEnd_25078 := by exact prefixLift 25078
  have htrace : WordTrace (prefixWord ++ tailWord_25078) baseStart_25078 baseEnd_25078 := by
    simpa [prefixWord, tailWord_25078, baseEnd_25078] using wordTrace_append hprefix tailTrace_25078
  have hstable : (prefixWord ++ tailWord_25078).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25078).length < 2 ^ (prefixWord ++ tailWord_25078).sum := by decide
  have hdescent : baseEnd_25078 < baseStart_25078 := by decide
  rcases family_descends (prefixWord ++ tailWord_25078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25080 : List Nat := [2, 1, 2, 1, 1, 4, 1, 7]
def baseStart_25080 : Nat := 118140960795 + 25080 * 2 ^ 59
def prefixEnd_25080 : Nat := 4983230072969 + 3 ^ 40 * 25080 * 2
def baseEnd_25080 : Nat := 7631463593995323309431

theorem tailTrace_25080 : CollatzResearch.WordTrace tailWord_25080 prefixEnd_25080 7631463593995323309431 := by
  unfold tailWord_25080
  simp only [CollatzResearch.WordTrace]
  refine ⟨457371374573459084048347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 609828499431278778731129 457371374573459084048347)
  ·
    refine ⟨686057061860188626072521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 457371374573459084048347 686057061860188626072521)
    ·
      refine ⟨514542796395141469554391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 686057061860188626072521 514542796395141469554391)
      ·
        refine ⟨771814194592712204331587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 514542796395141469554391 771814194592712204331587)
        ·
          refine ⟨1157721291889068306497381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 771814194592712204331587 1157721291889068306497381)
          ·
            refine ⟨217072742229200307468259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1157721291889068306497381 217072742229200307468259)
            ·
              refine ⟨325609113343800461202389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217072742229200307468259 325609113343800461202389)
              ·
                refine ⟨7631463593995323309431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 325609113343800461202389 7631463593995323309431)
                ·
                  rfl

theorem cell19_25080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 7].length) (baseStart_25080 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_25080 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_25080 prefixEnd_25080 := by exact prefixLift 25080
  have htrace : WordTrace (prefixWord ++ tailWord_25080) baseStart_25080 baseEnd_25080 := by
    simpa [prefixWord, tailWord_25080, baseEnd_25080] using wordTrace_append hprefix tailTrace_25080
  have hstable : (prefixWord ++ tailWord_25080).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25080).length < 2 ^ (prefixWord ++ tailWord_25080).sum := by decide
  have hdescent : baseEnd_25080 < baseStart_25080 := by decide
  rcases family_descends (prefixWord ++ tailWord_25080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25099 : List Nat := [1, 1, 1, 1, 7, 8]
def baseStart_25099 : Nat := 118140960795 + 25099 * 2 ^ 59
def prefixEnd_25099 : Nat := 4983230072969 + 3 ^ 40 * 25099 * 2
def baseEnd_25099 : Nat := 848582778423212098573

theorem tailTrace_25099 : CollatzResearch.WordTrace tailWord_25099 prefixEnd_25099 848582778423212098573 := by
  unfold tailWord_25099
  simp only [CollatzResearch.WordTrace]
  refine ⟨915435736078084413038351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 610290490718722942025567 915435736078084413038351)
  ·
    refine ⟨1373153604117126619557527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 915435736078084413038351 1373153604117126619557527)
    ·
      refine ⟨2059730406175689929336291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1373153604117126619557527 2059730406175689929336291)
      ·
        refine ⟨3089595609263534894004437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2059730406175689929336291 3089595609263534894004437)
        ·
          refine ⟨72412397092114099078229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 3089595609263534894004437 72412397092114099078229)
          ·
            refine ⟨848582778423212098573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 72412397092114099078229 848582778423212098573)
            ·
              rfl

theorem cell19_25099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 8].length) (baseStart_25099 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_25099 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_25099 prefixEnd_25099 := by exact prefixLift 25099
  have htrace : WordTrace (prefixWord ++ tailWord_25099) baseStart_25099 baseEnd_25099 := by
    simpa [prefixWord, tailWord_25099, baseEnd_25099] using wordTrace_append hprefix tailTrace_25099
  have hstable : (prefixWord ++ tailWord_25099).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25099).length < 2 ^ (prefixWord ++ tailWord_25099).sum := by decide
  have hdescent : baseEnd_25099 < baseStart_25099 := by decide
  rcases family_descends (prefixWord ++ tailWord_25099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25116 : List Nat := [2, 2, 3, 1, 2, 2, 3, 4]
def baseStart_25116 : Nat := 118140960795 + 25116 * 2 ^ 59
def prefixEnd_25116 : Nat := 4983230072969 + 3 ^ 40 * 25116 * 2
def baseEnd_25116 : Nat := 7642417847957906509333

theorem tailTrace_25116 : CollatzResearch.WordTrace tailWord_25116 prefixEnd_25116 7642417847957906509333 := by
  unfold tailWord_25116
  simp only [CollatzResearch.WordTrace]
  refine ⟨458027888508248158203601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 610703851344330877604801 458027888508248158203601)
  ·
    refine ⟨343520916381186118652701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 458027888508248158203601 343520916381186118652701)
    ·
      refine ⟨128820343642944794494763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 343520916381186118652701 128820343642944794494763)
      ·
        refine ⟨193230515464417191742145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128820343642944794494763 193230515464417191742145)
        ·
          refine ⟨144922886598312893806609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193230515464417191742145 144922886598312893806609)
          ·
            refine ⟨108692164948734670354957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144922886598312893806609 108692164948734670354957)
            ·
              refine ⟨40759561855775501383109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108692164948734670354957 40759561855775501383109)
              ·
                refine ⟨7642417847957906509333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40759561855775501383109 7642417847957906509333)
                ·
                  rfl

theorem cell19_25116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 4].length) (baseStart_25116 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_25116 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_25116 prefixEnd_25116 := by exact prefixLift 25116
  have htrace : WordTrace (prefixWord ++ tailWord_25116) baseStart_25116 baseEnd_25116 := by
    simpa [prefixWord, tailWord_25116, baseEnd_25116] using wordTrace_append hprefix tailTrace_25116
  have hstable : (prefixWord ++ tailWord_25116).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25116).length < 2 ^ (prefixWord ++ tailWord_25116).sum := by decide
  have hdescent : baseEnd_25116 < baseStart_25116 := by decide
  rcases family_descends (prefixWord ++ tailWord_25116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25137 : List Nat := [1, 2, 2, 3, 1, 1, 2, 7]
def baseStart_25137 : Nat := 118140960795 + 25137 * 2 ^ 59
def prefixEnd_25137 : Nat := 4983230072969 + 3 ^ 40 * 25137 * 2
def baseEnd_25137 : Nat := 7648807829436080042609

theorem tailTrace_25137 : CollatzResearch.WordTrace tailWord_25137 prefixEnd_25137 7648807829436080042609 := by
  unfold tailWord_25137
  simp only [CollatzResearch.WordTrace]
  refine ⟨916821709940416902921665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 611214473293611268614443 916821709940416902921665)
  ·
    refine ⟨687616282455312677191249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 916821709940416902921665 687616282455312677191249)
    ·
      refine ⟨515712211841484507893437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 687616282455312677191249 515712211841484507893437)
      ·
        refine ⟨193392079440556690460039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 515712211841484507893437 193392079440556690460039)
        ·
          refine ⟨290088119160835035690059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193392079440556690460039 290088119160835035690059)
          ·
            refine ⟨435132178741252553535089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290088119160835035690059 435132178741252553535089)
            ·
              refine ⟨326349134055939415151317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 435132178741252553535089 326349134055939415151317)
              ·
                refine ⟨7648807829436080042609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 326349134055939415151317 7648807829436080042609)
                ·
                  rfl

theorem cell19_25137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 7].length) (baseStart_25137 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_25137 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_25137 prefixEnd_25137 := by exact prefixLift 25137
  have htrace : WordTrace (prefixWord ++ tailWord_25137) baseStart_25137 baseEnd_25137 := by
    simpa [prefixWord, tailWord_25137, baseEnd_25137] using wordTrace_append hprefix tailTrace_25137
  have hstable : (prefixWord ++ tailWord_25137).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25137).length < 2 ^ (prefixWord ++ tailWord_25137).sum := by decide
  have hdescent : baseEnd_25137 < baseStart_25137 := by decide
  rcases family_descends (prefixWord ++ tailWord_25137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25175 : List Nat := [1, 1, 3, 2, 2, 2, 2, 6]
def baseStart_25175 : Nat := 118140960795 + 25175 * 2 ^ 59
def prefixEnd_25175 : Nat := 4983230072969 + 3 ^ 40 * 25175 * 2
def baseEnd_25175 : Nat := 7660370653063251198061

theorem tailTrace_25175 : CollatzResearch.WordTrace tailWord_25175 prefixEnd_25175 7660370653063251198061 := by
  unfold tailWord_25175
  simp only [CollatzResearch.WordTrace]
  refine ⟨918207683802749392804979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 612138455868499595203319 918207683802749392804979)
  ·
    refine ⟨1377311525704124089207469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 918207683802749392804979 1377311525704124089207469)
    ·
      refine ⟨516491822139046533452801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1377311525704124089207469 516491822139046533452801)
      ·
        refine ⟨387368866604284900089601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 516491822139046533452801 387368866604284900089601)
        ·
          refine ⟨290526649953213675067201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 387368866604284900089601 290526649953213675067201)
          ·
            refine ⟨217894987464910256300401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290526649953213675067201 217894987464910256300401)
            ·
              refine ⟨163421240598682692225301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217894987464910256300401 163421240598682692225301)
              ·
                refine ⟨7660370653063251198061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 163421240598682692225301 7660370653063251198061)
                ·
                  rfl

theorem cell19_25175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 6].length) (baseStart_25175 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_25175 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_25175 prefixEnd_25175 := by exact prefixLift 25175
  have htrace : WordTrace (prefixWord ++ tailWord_25175) baseStart_25175 baseEnd_25175 := by
    simpa [prefixWord, tailWord_25175, baseEnd_25175] using wordTrace_append hprefix tailTrace_25175
  have hstable : (prefixWord ++ tailWord_25175).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25175).length < 2 ^ (prefixWord ++ tailWord_25175).sum := by decide
  have hdescent : baseEnd_25175 < baseStart_25175 := by decide
  rcases family_descends (prefixWord ++ tailWord_25175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25182 : List Nat := [4, 4, 1, 2, 2, 1, 2, 3]
def baseStart_25182 : Nat := 118140960795 + 25182 * 2 ^ 59
def prefixEnd_25182 : Nat := 4983230072969 + 3 ^ 40 * 25182 * 2
def baseEnd_25182 : Nat := 7662500646889309042487

theorem tailTrace_25182 : CollatzResearch.WordTrace tailWord_25182 prefixEnd_25182 7662500646889309042487 := by
  unfold tailWord_25182
  simp only [CollatzResearch.WordTrace]
  refine ⟨114807874347173698538725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 612308663184926392206533 114807874347173698538725)
  ·
    refine ⟨21526476440095068476011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114807874347173698538725 21526476440095068476011)
    ·
      refine ⟨32289714660142602714017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21526476440095068476011 32289714660142602714017)
      ·
        refine ⟨24217285995106952035513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32289714660142602714017 24217285995106952035513)
        ·
          refine ⟨18162964496330214026635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24217285995106952035513 18162964496330214026635)
          ·
            refine ⟨27244446744495321039953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18162964496330214026635 27244446744495321039953)
            ·
              refine ⟨20433335058371490779965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27244446744495321039953 20433335058371490779965)
              ·
                refine ⟨7662500646889309042487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20433335058371490779965 7662500646889309042487)
                ·
                  rfl

theorem cell19_25182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_25182 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_25182 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_25182 prefixEnd_25182 := by exact prefixLift 25182
  have htrace : WordTrace (prefixWord ++ tailWord_25182) baseStart_25182 baseEnd_25182 := by
    simpa [prefixWord, tailWord_25182, baseEnd_25182] using wordTrace_append hprefix tailTrace_25182
  have hstable : (prefixWord ++ tailWord_25182).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25182).length < 2 ^ (prefixWord ++ tailWord_25182).sum := by decide
  have hdescent : baseEnd_25182 < baseStart_25182 := by decide
  rcases family_descends (prefixWord ++ tailWord_25182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25186 : List Nat := [3, 3, 2, 3, 1, 2, 2, 3]
def baseStart_25186 : Nat := 118140960795 + 25186 * 2 ^ 59
def prefixEnd_25186 : Nat := 4983230072969 + 3 ^ 40 * 25186 * 2
def baseEnd_25186 : Nat := 7663717786218484953587

theorem tailTrace_25186 : CollatzResearch.WordTrace tailWord_25186 prefixEnd_25186 7663717786218484953587 := by
  unfold tailWord_25186
  simp only [CollatzResearch.WordTrace]
  refine ⟨229652221690724567863853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 612405924508598847636941 229652221690724567863853)
  ·
    refine ⟨86119583134021712948945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229652221690724567863853 86119583134021712948945)
    ·
      refine ⟨64589687350516284711709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86119583134021712948945 64589687350516284711709)
      ·
        refine ⟨24221132756443606766891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64589687350516284711709 24221132756443606766891)
        ·
          refine ⟨36331699134665410150337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24221132756443606766891 36331699134665410150337)
          ·
            refine ⟨27248774350999057612753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36331699134665410150337 27248774350999057612753)
            ·
              refine ⟨20436580763249293209565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27248774350999057612753 20436580763249293209565)
              ·
                refine ⟨7663717786218484953587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20436580763249293209565 7663717786218484953587)
                ·
                  rfl

theorem cell19_25186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 3].length) (baseStart_25186 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_25186 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_25186 prefixEnd_25186 := by exact prefixLift 25186
  have htrace : WordTrace (prefixWord ++ tailWord_25186) baseStart_25186 baseEnd_25186 := by
    simpa [prefixWord, tailWord_25186, baseEnd_25186] using wordTrace_append hprefix tailTrace_25186
  have hstable : (prefixWord ++ tailWord_25186).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25186).length < 2 ^ (prefixWord ++ tailWord_25186).sum := by decide
  have hdescent : baseEnd_25186 < baseStart_25186 := by decide
  rcases family_descends (prefixWord ++ tailWord_25186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25230 : List Nat := [4, 1, 1, 3, 1, 1, 4, 4]
def baseStart_25230 : Nat := 118140960795 + 25230 * 2 ^ 59
def prefixEnd_25230 : Nat := 4983230072969 + 3 ^ 40 * 25230 * 2
def baseEnd_25230 : Nat := 7677106318839419975689

theorem tailTrace_25230 : CollatzResearch.WordTrace tailWord_25230 prefixEnd_25230 7677106318839419975689 := by
  unfold tailWord_25230
  simp only [CollatzResearch.WordTrace]
  refine ⟨115026712325436723257143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 613475799068995857371429 115026712325436723257143)
  ·
    refine ⟨172540068488155084885715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115026712325436723257143 172540068488155084885715)
    ·
      refine ⟨258810102732232627328573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172540068488155084885715 258810102732232627328573)
      ·
        refine ⟨97053788524587235248215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 258810102732232627328573 97053788524587235248215)
        ·
          refine ⟨145580682786880852872323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97053788524587235248215 145580682786880852872323)
          ·
            refine ⟨218371024180321279308485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145580682786880852872323 218371024180321279308485)
            ·
              refine ⟨40944567033810239870341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 218371024180321279308485 40944567033810239870341)
              ·
                refine ⟨7677106318839419975689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40944567033810239870341 7677106318839419975689)
                ·
                  rfl

theorem cell19_25230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_25230 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_25230 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_25230 prefixEnd_25230 := by exact prefixLift 25230
  have htrace : WordTrace (prefixWord ++ tailWord_25230) baseStart_25230 baseEnd_25230 := by
    simpa [prefixWord, tailWord_25230, baseEnd_25230] using wordTrace_append hprefix tailTrace_25230
  have hstable : (prefixWord ++ tailWord_25230).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25230).length < 2 ^ (prefixWord ++ tailWord_25230).sum := by decide
  have hdescent : baseEnd_25230 < baseStart_25230 := by decide
  rcases family_descends (prefixWord ++ tailWord_25230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25281 : List Nat := [1, 2, 6, 2, 2, 1, 1, 4]
def baseStart_25281 : Nat := 118140960795 + 25281 * 2 ^ 59
def prefixEnd_25281 : Nat := 4983230072969 + 3 ^ 40 * 25281 * 2
def baseEnd_25281 : Nat := 7692624845286412842217

theorem tailTrace_25281 : CollatzResearch.WordTrace tailWord_25281 prefixEnd_25281 7692624845286412842217 := by
  unfold tailWord_25281
  simp only [CollatzResearch.WordTrace]
  refine ⟨922073821418729496163697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 614715880945819664109131 922073821418729496163697)
  ·
    refine ⟨691555366064047122122773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 922073821418729496163697 691555366064047122122773)
    ·
      refine ⟨32416657784252208849505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 691555366064047122122773 32416657784252208849505)
      ·
        refine ⟨24312493338189156637129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32416657784252208849505 24312493338189156637129)
        ·
          refine ⟨18234370003641867477847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24312493338189156637129 18234370003641867477847)
          ·
            refine ⟨27351555005462801216771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18234370003641867477847 27351555005462801216771)
            ·
              refine ⟨41027332508194201825157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27351555005462801216771 41027332508194201825157)
              ·
                refine ⟨7692624845286412842217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41027332508194201825157 7692624845286412842217)
                ·
                  rfl

theorem cell19_25281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 4].length) (baseStart_25281 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_25281 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_25281 prefixEnd_25281 := by exact prefixLift 25281
  have htrace : WordTrace (prefixWord ++ tailWord_25281) baseStart_25281 baseEnd_25281 := by
    simpa [prefixWord, tailWord_25281, baseEnd_25281] using wordTrace_append hprefix tailTrace_25281
  have hstable : (prefixWord ++ tailWord_25281).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25281).length < 2 ^ (prefixWord ++ tailWord_25281).sum := by decide
  have hdescent : baseEnd_25281 < baseStart_25281 := by decide
  rcases family_descends (prefixWord ++ tailWord_25281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25306 : List Nat := [3, 1, 1, 2, 2, 2, 5, 3]
def baseStart_25306 : Nat := 118140960795 + 25306 * 2 ^ 59
def prefixEnd_25306 : Nat := 4983230072969 + 3 ^ 40 * 25306 * 2
def baseEnd_25306 : Nat := 7700231966093762286593

theorem tailTrace_25306 : CollatzResearch.WordTrace tailWord_25306 prefixEnd_25306 7700231966093762286593 := by
  unfold tailWord_25306
  simp only [CollatzResearch.WordTrace]
  refine ⟨230746411582039691455943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 615323764218772510549181 230746411582039691455943)
  ·
    refine ⟨346119617373059537183915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230746411582039691455943 346119617373059537183915)
    ·
      refine ⟨519179426059589305775873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346119617373059537183915 519179426059589305775873)
      ·
        refine ⟨389384569544691979331905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 519179426059589305775873 389384569544691979331905)
        ·
          refine ⟨292038427158518984498929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 389384569544691979331905 292038427158518984498929)
          ·
            refine ⟨219028820368889238374197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 292038427158518984498929 219028820368889238374197)
            ·
              refine ⟨20533951909583366097581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 219028820368889238374197 20533951909583366097581)
              ·
                refine ⟨7700231966093762286593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20533951909583366097581 7700231966093762286593)
                ·
                  rfl

theorem cell19_25306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 3].length) (baseStart_25306 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_25306 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_25306 prefixEnd_25306 := by exact prefixLift 25306
  have htrace : WordTrace (prefixWord ++ tailWord_25306) baseStart_25306 baseEnd_25306 := by
    simpa [prefixWord, tailWord_25306, baseEnd_25306] using wordTrace_append hprefix tailTrace_25306
  have hstable : (prefixWord ++ tailWord_25306).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25306).length < 2 ^ (prefixWord ++ tailWord_25306).sum := by decide
  have hdescent : baseEnd_25306 < baseStart_25306 := by decide
  rcases family_descends (prefixWord ++ tailWord_25306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25327 : List Nat := [1, 1, 2, 1, 5, 3, 6]
def baseStart_25327 : Nat := 118140960795 + 25327 * 2 ^ 59
def prefixEnd_25327 : Nat := 4983230072969 + 3 ^ 40 * 25327 * 2
def baseEnd_25327 : Nat := 2568873982523978606623

theorem tailTrace_25327 : CollatzResearch.WordTrace tailWord_25327 prefixEnd_25327 2568873982523978606623 := by
  unfold tailWord_25327
  simp only [CollatzResearch.WordTrace]
  refine ⟨923751579252079352338235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 615834386168052901558823 923751579252079352338235)
  ·
    refine ⟨1385627368878119028507353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 923751579252079352338235 1385627368878119028507353)
    ·
      refine ⟨1039220526658589271380515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1385627368878119028507353 1039220526658589271380515)
      ·
        refine ⟨1558830789987883907070773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1039220526658589271380515 1558830789987883907070773)
        ·
          refine ⟨146140386561364116287885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1558830789987883907070773 146140386561364116287885)
          ·
            refine ⟨54802644960511543607957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146140386561364116287885 54802644960511543607957)
            ·
              refine ⟨2568873982523978606623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 54802644960511543607957 2568873982523978606623)
              ·
                rfl

theorem cell19_25327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 6].length) (baseStart_25327 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_25327 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_25327 prefixEnd_25327 := by exact prefixLift 25327
  have htrace : WordTrace (prefixWord ++ tailWord_25327) baseStart_25327 baseEnd_25327 := by
    simpa [prefixWord, tailWord_25327, baseEnd_25327] using wordTrace_append hprefix tailTrace_25327
  have hstable : (prefixWord ++ tailWord_25327).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25327).length < 2 ^ (prefixWord ++ tailWord_25327).sum := by decide
  have hdescent : baseEnd_25327 < baseStart_25327 := by decide
  rcases family_descends (prefixWord ++ tailWord_25327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25365 : List Nat := [1, 3, 2, 1, 2, 2, 3, 5]
def baseStart_25365 : Nat := 118140960795 + 25365 * 2 ^ 59
def prefixEnd_25365 : Nat := 4983230072969 + 3 ^ 40 * 25365 * 2
def baseEnd_25365 : Nat := 7718184771199106975321

theorem tailTrace_25365 : CollatzResearch.WordTrace tailWord_25365 prefixEnd_25365 7718184771199106975321 := by
  unfold tailWord_25365
  simp only [CollatzResearch.WordTrace]
  refine ⟨925137553114411842221549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 616758368742941228147699 925137553114411842221549)
  ·
    refine ⟨346926582417904440833081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 925137553114411842221549 346926582417904440833081)
    ·
      refine ⟨260194936813428330624811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 346926582417904440833081 260194936813428330624811)
      ·
        refine ⟨390292405220142495937217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260194936813428330624811 390292405220142495937217)
        ·
          refine ⟨292719303915106871952913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 390292405220142495937217 292719303915106871952913)
          ·
            refine ⟨219539477936330153964685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 292719303915106871952913 219539477936330153964685)
            ·
              refine ⟨82327304226123807736757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 219539477936330153964685 82327304226123807736757)
              ·
                refine ⟨7718184771199106975321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82327304226123807736757 7718184771199106975321)
                ·
                  rfl

theorem cell19_25365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 5].length) (baseStart_25365 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_25365 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_25365 prefixEnd_25365 := by exact prefixLift 25365
  have htrace : WordTrace (prefixWord ++ tailWord_25365) baseStart_25365 baseEnd_25365 := by
    simpa [prefixWord, tailWord_25365, baseEnd_25365] using wordTrace_append hprefix tailTrace_25365
  have hstable : (prefixWord ++ tailWord_25365).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25365).length < 2 ^ (prefixWord ++ tailWord_25365).sum := by decide
  have hdescent : baseEnd_25365 < baseStart_25365 := by decide
  rcases family_descends (prefixWord ++ tailWord_25365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25380 : List Nat := [2, 3, 1, 3, 4, 1, 5]
def baseStart_25380 : Nat := 118140960795 + 25380 * 2 ^ 59
def prefixEnd_25380 : Nat := 4983230072969 + 3 ^ 40 * 25380 * 2
def baseEnd_25380 : Nat := 2574249681227838880649

theorem tailTrace_25380 : CollatzResearch.WordTrace tailWord_25380 prefixEnd_25380 2574249681227838880649 := by
  unfold tailWord_25380
  simp only [CollatzResearch.WordTrace]
  refine ⟨462842324030034702008797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 617123098706712936011729 462842324030034702008797)
  ·
    refine ⟨173565871511263013253299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 462842324030034702008797 173565871511263013253299)
    ·
      refine ⟨260348807266894519879949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173565871511263013253299 260348807266894519879949)
      ·
        refine ⟨97630802725085444954981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 260348807266894519879949 97630802725085444954981)
        ·
          refine ⟨18305775510953520929059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97630802725085444954981 18305775510953520929059)
          ·
            refine ⟨27458663266430281393589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18305775510953520929059 27458663266430281393589)
            ·
              refine ⟨2574249681227838880649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27458663266430281393589 2574249681227838880649)
              ·
                rfl

theorem cell19_25380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 5].length) (baseStart_25380 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_25380 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_25380 prefixEnd_25380 := by exact prefixLift 25380
  have htrace : WordTrace (prefixWord ++ tailWord_25380) baseStart_25380 baseEnd_25380 := by
    simpa [prefixWord, tailWord_25380, baseEnd_25380] using wordTrace_append hprefix tailTrace_25380
  have hstable : (prefixWord ++ tailWord_25380).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25380).length < 2 ^ (prefixWord ++ tailWord_25380).sum := by decide
  have hdescent : baseEnd_25380 < baseStart_25380 := by decide
  rcases family_descends (prefixWord ++ tailWord_25380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25454 : List Nat := [4, 1, 2, 3, 3, 1, 1, 4]
def baseStart_25454 : Nat := 118140960795 + 25454 * 2 ^ 59
def prefixEnd_25454 : Nat := 4983230072969 + 3 ^ 40 * 25454 * 2
def baseEnd_25454 : Nat := 7745266121273270997301

theorem tailTrace_25454 : CollatzResearch.WordTrace tailWord_25454 prefixEnd_25454 7745266121273270997301 := by
  unfold tailWord_25454
  simp only [CollatzResearch.WordTrace]
  refine ⟨116047956223997505276427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 618922433194653361474277 116047956223997505276427)
  ·
    refine ⟨174071934335996257914641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116047956223997505276427 174071934335996257914641)
    ·
      refine ⟨130553950751997193435981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174071934335996257914641 130553950751997193435981)
      ·
        refine ⟨48957731531998947538493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130553950751997193435981 48957731531998947538493)
        ·
          refine ⟨18359149324499605326935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48957731531998947538493 18359149324499605326935)
          ·
            refine ⟨27538723986749407990403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18359149324499605326935 27538723986749407990403)
            ·
              refine ⟨41308085980124111985605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27538723986749407990403 41308085980124111985605)
              ·
                refine ⟨7745266121273270997301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41308085980124111985605 7745266121273270997301)
                ·
                  rfl

theorem cell19_25454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_25454 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_25454 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_25454 prefixEnd_25454 := by exact prefixLift 25454
  have htrace : WordTrace (prefixWord ++ tailWord_25454) baseStart_25454 baseEnd_25454 := by
    simpa [prefixWord, tailWord_25454, baseEnd_25454] using wordTrace_append hprefix tailTrace_25454
  have hstable : (prefixWord ++ tailWord_25454).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25454).length < 2 ^ (prefixWord ++ tailWord_25454).sum := by decide
  have hdescent : baseEnd_25454 < baseStart_25454 := by decide
  rcases family_descends (prefixWord ++ tailWord_25454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25477 : List Nat := [1, 3, 1, 1, 3, 4, 3, 3]
def baseStart_25477 : Nat := 118140960795 + 25477 * 2 ^ 59
def prefixEnd_25477 : Nat := 4983230072969 + 3 ^ 40 * 25477 * 2
def baseEnd_25477 : Nat := 7752264672416032486127

theorem tailTrace_25477 : CollatzResearch.WordTrace tailWord_25477 prefixEnd_25477 7752264672416032486127 := by
  unfold tailWord_25477
  simp only [CollatzResearch.WordTrace]
  refine ⟨929222528708654970298685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 619481685805769980199123 929222528708654970298685)
  ·
    refine ⟨348458448265745613862007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 929222528708654970298685 348458448265745613862007)
    ·
      refine ⟨522687672398618420793011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348458448265745613862007 522687672398618420793011)
      ·
        refine ⟨784031508597927631189517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 522687672398618420793011 784031508597927631189517)
        ·
          refine ⟨294011815724222861696069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 784031508597927631189517 294011815724222861696069)
          ·
            refine ⟨55127215448291786568013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 294011815724222861696069 55127215448291786568013)
            ·
              refine ⟨20672705793109419963005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55127215448291786568013 20672705793109419963005)
              ·
                refine ⟨7752264672416032486127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20672705793109419963005 7752264672416032486127)
                ·
                  rfl

theorem cell19_25477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 3].length) (baseStart_25477 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_25477 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_25477 prefixEnd_25477 := by exact prefixLift 25477
  have htrace : WordTrace (prefixWord ++ tailWord_25477) baseStart_25477 baseEnd_25477 := by
    simpa [prefixWord, tailWord_25477, baseEnd_25477] using wordTrace_append hprefix tailTrace_25477
  have hstable : (prefixWord ++ tailWord_25477).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25477).length < 2 ^ (prefixWord ++ tailWord_25477).sum := by decide
  have hdescent : baseEnd_25477 < baseStart_25477 := by decide
  rcases family_descends (prefixWord ++ tailWord_25477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25526 : List Nat := [5, 1, 4, 1, 1, 2, 2, 3]
def baseStart_25526 : Nat := 118140960795 + 25526 * 2 ^ 59
def prefixEnd_25526 : Nat := 4983230072969 + 3 ^ 40 * 25526 * 2
def baseEnd_25526 : Nat := 7767174629198437397105

theorem tailTrace_25526 : CollatzResearch.WordTrace tailWord_25526 prefixEnd_25526 7767174629198437397105 := by
  unfold tailWord_25526
  simp only [CollatzResearch.WordTrace]
  refine ⟨58188106595696021177027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 620673137020757559221621 58188106595696021177027)
  ·
    refine ⟨87282159893544031765541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58188106595696021177027 87282159893544031765541)
    ·
      refine ⟨16365404980039505956039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87282159893544031765541 16365404980039505956039)
      ·
        refine ⟨24548107470059258934059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16365404980039505956039 24548107470059258934059)
        ·
          refine ⟨36822161205088888401089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24548107470059258934059 36822161205088888401089)
          ·
            refine ⟨27616620903816666300817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36822161205088888401089 27616620903816666300817)
            ·
              refine ⟨20712465677862499725613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27616620903816666300817 20712465677862499725613)
              ·
                refine ⟨7767174629198437397105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20712465677862499725613 7767174629198437397105)
                ·
                  rfl

theorem cell19_25526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_25526 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_25526 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_25526 prefixEnd_25526 := by exact prefixLift 25526
  have htrace : WordTrace (prefixWord ++ tailWord_25526) baseStart_25526 baseEnd_25526 := by
    simpa [prefixWord, tailWord_25526, baseEnd_25526] using wordTrace_append hprefix tailTrace_25526
  have hstable : (prefixWord ++ tailWord_25526).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25526).length < 2 ^ (prefixWord ++ tailWord_25526).sum := by decide
  have hdescent : baseEnd_25526 < baseStart_25526 := by decide
  rcases family_descends (prefixWord ++ tailWord_25526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25536 : List Nat := [2, 1, 1, 2, 3, 4, 1, 5]
def baseStart_25536 : Nat := 118140960795 + 25536 * 2 ^ 59
def prefixEnd_25536 : Nat := 4983230072969 + 3 ^ 40 * 25536 * 2
def baseEnd_25536 : Nat := 7770217477521377174855

theorem tailTrace_25536 : CollatzResearch.WordTrace tailWord_25536 prefixEnd_25536 7770217477521377174855 := by
  unfold tailWord_25536
  simp only [CollatzResearch.WordTrace]
  refine ⟨465687217747454023348231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 620916290329938697797641 465687217747454023348231)
  ·
    refine ⟨698530826621181035022347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 465687217747454023348231 698530826621181035022347)
    ·
      refine ⟨1047796239931771552533521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 698530826621181035022347 1047796239931771552533521)
      ·
        refine ⟨785847179948828664400141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1047796239931771552533521 785847179948828664400141)
        ·
          refine ⟨294692692480810749150053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 785847179948828664400141 294692692480810749150053)
          ·
            refine ⟨55254879840152015465635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 294692692480810749150053 55254879840152015465635)
            ·
              refine ⟨82882319760228023198453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55254879840152015465635 82882319760228023198453)
              ·
                refine ⟨7770217477521377174855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82882319760228023198453 7770217477521377174855)
                ·
                  rfl

theorem cell19_25536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 5].length) (baseStart_25536 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_25536 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_25536 prefixEnd_25536 := by exact prefixLift 25536
  have htrace : WordTrace (prefixWord ++ tailWord_25536) baseStart_25536 baseEnd_25536 := by
    simpa [prefixWord, tailWord_25536, baseEnd_25536] using wordTrace_append hprefix tailTrace_25536
  have hstable : (prefixWord ++ tailWord_25536).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25536).length < 2 ^ (prefixWord ++ tailWord_25536).sum := by decide
  have hdescent : baseEnd_25536 < baseStart_25536 := by decide
  rcases family_descends (prefixWord ++ tailWord_25536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25570 : List Nat := [3, 3, 3, 1, 1, 2, 2, 4]
def baseStart_25570 : Nat := 118140960795 + 25570 * 2 ^ 59
def prefixEnd_25570 : Nat := 4983230072969 + 3 ^ 40 * 25570 * 2
def baseEnd_25570 : Nat := 7780563161819372419207

theorem tailTrace_25570 : CollatzResearch.WordTrace tailWord_25570 prefixEnd_25570 7780563161819372419207 := by
  unfold tailWord_25570
  simp only [CollatzResearch.WordTrace]
  refine ⟨233153629342932963358541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 621743011581154568956109 233153629342932963358541)
  ·
    refine ⟨87432611003599861259453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233153629342932963358541 87432611003599861259453)
    ·
      refine ⟨32787229126349947972295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87432611003599861259453 32787229126349947972295)
      ·
        refine ⟨49180843689524921958443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32787229126349947972295 49180843689524921958443)
        ·
          refine ⟨73771265534287382937665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49180843689524921958443 73771265534287382937665)
          ·
            refine ⟨55328449150715537203249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73771265534287382937665 55328449150715537203249)
            ·
              refine ⟨41496336863036652902437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55328449150715537203249 41496336863036652902437)
              ·
                refine ⟨7780563161819372419207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41496336863036652902437 7780563161819372419207)
                ·
                  rfl

theorem cell19_25570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 4].length) (baseStart_25570 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_25570 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_25570 prefixEnd_25570 := by exact prefixLift 25570
  have htrace : WordTrace (prefixWord ++ tailWord_25570) baseStart_25570 baseEnd_25570 := by
    simpa [prefixWord, tailWord_25570, baseEnd_25570] using wordTrace_append hprefix tailTrace_25570
  have hstable : (prefixWord ++ tailWord_25570).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25570).length < 2 ^ (prefixWord ++ tailWord_25570).sum := by decide
  have hdescent : baseEnd_25570 < baseStart_25570 := by decide
  rcases family_descends (prefixWord ++ tailWord_25570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25631 : List Nat := [1, 1, 2, 4, 1, 3, 3, 4]
def baseStart_25631 : Nat := 118140960795 + 25631 * 2 ^ 59
def prefixEnd_25631 : Nat := 4983230072969 + 3 ^ 40 * 25631 * 2
def baseEnd_25631 : Nat := 7799124536589305063485

theorem tailTrace_25631 : CollatzResearch.WordTrace tailWord_25631 prefixEnd_25631 7799124536589305063485 := by
  unfold tailWord_25631
  simp only [CollatzResearch.WordTrace]
  refine ⟨934839370150739271404747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 623226246767159514269831 934839370150739271404747)
  ·
    refine ⟨1402259055226108907107121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 934839370150739271404747 1402259055226108907107121)
    ·
      refine ⟨1051694291419581680330341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1402259055226108907107121 1051694291419581680330341)
      ·
        refine ⟨197192679641171565061939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1051694291419581680330341 197192679641171565061939)
        ·
          refine ⟨295789019461757347592909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197192679641171565061939 295789019461757347592909)
          ·
            refine ⟨110920882298159005347341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 295789019461757347592909 110920882298159005347341)
            ·
              refine ⟨41595330861809627005253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110920882298159005347341 41595330861809627005253)
              ·
                refine ⟨7799124536589305063485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41595330861809627005253 7799124536589305063485)
                ·
                  rfl

theorem cell19_25631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 4].length) (baseStart_25631 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_25631 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_25631 prefixEnd_25631 := by exact prefixLift 25631
  have htrace : WordTrace (prefixWord ++ tailWord_25631) baseStart_25631 baseEnd_25631 := by
    simpa [prefixWord, tailWord_25631, baseEnd_25631] using wordTrace_append hprefix tailTrace_25631
  have hstable : (prefixWord ++ tailWord_25631).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25631).length < 2 ^ (prefixWord ++ tailWord_25631).sum := by decide
  have hdescent : baseEnd_25631 < baseStart_25631 := by decide
  rcases family_descends (prefixWord ++ tailWord_25631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25705 : List Nat := [1, 2, 1, 1, 1, 8, 2, 3]
def baseStart_25705 : Nat := 118140960795 + 25705 * 2 ^ 59
def prefixEnd_25705 : Nat := 4983230072969 + 3 ^ 40 * 25705 * 2
def baseEnd_25705 : Nat := 7821641614179059418839

theorem tailTrace_25705 : CollatzResearch.WordTrace tailWord_25705 prefixEnd_25705 7821641614179059418839 := by
  unfold tailWord_25705
  simp only [CollatzResearch.WordTrace]
  refine ⟨937538371882649909598569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 625025581255099939732379 937538371882649909598569)
  ·
    refine ⟨703153778911987432198927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 937538371882649909598569 703153778911987432198927)
    ·
      refine ⟨1054730668367981148298391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 703153778911987432198927 1054730668367981148298391)
      ·
        refine ⟨1582096002551971722447587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1054730668367981148298391 1582096002551971722447587)
        ·
          refine ⟨2373144003827957583671381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1582096002551971722447587 2373144003827957583671381)
          ·
            refine ⟨27810281294858877933649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 2373144003827957583671381 27810281294858877933649)
            ·
              refine ⟨20857710971144158450237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27810281294858877933649 20857710971144158450237)
              ·
                refine ⟨7821641614179059418839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20857710971144158450237 7821641614179059418839)
                ·
                  rfl

theorem cell19_25705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 3].length) (baseStart_25705 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_25705 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_25705 prefixEnd_25705 := by exact prefixLift 25705
  have htrace : WordTrace (prefixWord ++ tailWord_25705) baseStart_25705 baseEnd_25705 := by
    simpa [prefixWord, tailWord_25705, baseEnd_25705] using wordTrace_append hprefix tailTrace_25705
  have hstable : (prefixWord ++ tailWord_25705).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25705).length < 2 ^ (prefixWord ++ tailWord_25705).sum := by decide
  have hdescent : baseEnd_25705 < baseStart_25705 := by decide
  rcases family_descends (prefixWord ++ tailWord_25705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25728 : List Nat := [2, 1, 1, 2, 1, 3, 9]
def baseStart_25728 : Nat := 118140960795 + 25728 * 2 ^ 59
def prefixEnd_25728 : Nat := 4983230072969 + 3 ^ 40 * 25728 * 2
def baseEnd_25728 : Nat := 2609546721773940302555

theorem tailTrace_25728 : CollatzResearch.WordTrace tailWord_25728 prefixEnd_25728 2609546721773940302555 := by
  unfold tailWord_25728
  simp only [CollatzResearch.WordTrace]
  refine ⟨469188625399662418842919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 625584833866216558457225 469188625399662418842919)
  ·
    refine ⟨703782938099493628264379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 469188625399662418842919 703782938099493628264379)
    ·
      refine ⟨1055674407149240442396569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 703782938099493628264379 1055674407149240442396569)
      ·
        refine ⟨791755805361930331797427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1055674407149240442396569 791755805361930331797427)
        ·
          refine ⟨1187633708042895497696141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 791755805361930331797427 1187633708042895497696141)
          ·
            refine ⟨445362640516085811636053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1187633708042895497696141 445362640516085811636053)
            ·
              refine ⟨2609546721773940302555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 445362640516085811636053 2609546721773940302555)
              ·
                rfl

theorem cell19_25728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 9].length) (baseStart_25728 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_25728 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_25728 prefixEnd_25728 := by exact prefixLift 25728
  have htrace : WordTrace (prefixWord ++ tailWord_25728) baseStart_25728 baseEnd_25728 := by
    simpa [prefixWord, tailWord_25728, baseEnd_25728] using wordTrace_append hprefix tailTrace_25728
  have hstable : (prefixWord ++ tailWord_25728).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25728).length < 2 ^ (prefixWord ++ tailWord_25728).sum := by decide
  have hdescent : baseEnd_25728 < baseStart_25728 := by decide
  rcases family_descends (prefixWord ++ tailWord_25728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25747 : List Nat := [1, 1, 1, 2, 1, 2, 5, 6]
def baseStart_25747 : Nat := 118140960795 + 25747 * 2 ^ 59
def prefixEnd_25747 : Nat := 4983230072969 + 3 ^ 40 * 25747 * 2
def baseEnd_25747 : Nat := 7834421577135406485391

theorem tailTrace_25747 : CollatzResearch.WordTrace tailWord_25747 prefixEnd_25747 7834421577135406485391 := by
  unfold tailWord_25747
  simp only [CollatzResearch.WordTrace]
  refine ⟨939070237730491082627495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 626046825153660721751663 939070237730491082627495)
  ·
    refine ⟨1408605356595736623941243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 939070237730491082627495 1408605356595736623941243)
    ·
      refine ⟨2112908034893604935911865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1408605356595736623941243 2112908034893604935911865)
      ·
        refine ⟨1584681026170203701933899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2112908034893604935911865 1584681026170203701933899)
        ·
          refine ⟨2377021539255305552900849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1584681026170203701933899 2377021539255305552900849)
          ·
            refine ⟨1782766154441479164675637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2377021539255305552900849 1782766154441479164675637)
            ·
              refine ⟨167134326978888671688341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1782766154441479164675637 167134326978888671688341)
              ·
                refine ⟨7834421577135406485391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 167134326978888671688341 7834421577135406485391)
                ·
                  rfl

theorem cell19_25747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 6].length) (baseStart_25747 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_25747 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_25747 prefixEnd_25747 := by exact prefixLift 25747
  have htrace : WordTrace (prefixWord ++ tailWord_25747) baseStart_25747 baseEnd_25747 := by
    simpa [prefixWord, tailWord_25747, baseEnd_25747] using wordTrace_append hprefix tailTrace_25747
  have hstable : (prefixWord ++ tailWord_25747).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25747).length < 2 ^ (prefixWord ++ tailWord_25747).sum := by decide
  have hdescent : baseEnd_25747 < baseStart_25747 := by decide
  rcases family_descends (prefixWord ++ tailWord_25747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25764 : List Nat := [2, 3, 1, 2, 3, 1, 2, 5]
def baseStart_25764 : Nat := 118140960795 + 25764 * 2 ^ 59
def prefixEnd_25764 : Nat := 4983230072969 + 3 ^ 40 * 25764 * 2
def baseEnd_25764 : Nat := 7839594419284404107567

theorem tailTrace_25764 : CollatzResearch.WordTrace tailWord_25764 prefixEnd_25764 7839594419284404107567 := by
  unfold tailWord_25764
  simp only [CollatzResearch.WordTrace]
  refine ⟨469845139334451492998173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 626460185779268657330897 469845139334451492998173)
  ·
    refine ⟨176191927250419309874315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 469845139334451492998173 176191927250419309874315)
    ·
      refine ⟨264287890875628964811473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176191927250419309874315 264287890875628964811473)
      ·
        refine ⟨198215918156721723608605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264287890875628964811473 198215918156721723608605)
        ·
          refine ⟨74330969308770646353227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198215918156721723608605 74330969308770646353227)
          ·
            refine ⟨111496453963155969529841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74330969308770646353227 111496453963155969529841)
            ·
              refine ⟨83622340472366977147381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111496453963155969529841 83622340472366977147381)
              ·
                refine ⟨7839594419284404107567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83622340472366977147381 7839594419284404107567)
                ·
                  rfl

theorem cell19_25764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 5].length) (baseStart_25764 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_25764 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_25764 prefixEnd_25764 := by exact prefixLift 25764
  have htrace : WordTrace (prefixWord ++ tailWord_25764) baseStart_25764 baseEnd_25764 := by
    simpa [prefixWord, tailWord_25764, baseEnd_25764] using wordTrace_append hprefix tailTrace_25764
  have hstable : (prefixWord ++ tailWord_25764).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25764).length < 2 ^ (prefixWord ++ tailWord_25764).sum := by decide
  have hdescent : baseEnd_25764 < baseStart_25764 := by decide
  rcases family_descends (prefixWord ++ tailWord_25764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25785 : List Nat := [1, 2, 1, 4, 1, 10]
def baseStart_25785 : Nat := 118140960795 + 25785 * 2 ^ 59
def prefixEnd_25785 : Nat := 4983230072969 + 3 ^ 40 * 25785 * 2
def baseEnd_25785 : Nat := 871776044529175293427

theorem tailTrace_25785 : CollatzResearch.WordTrace tailWord_25785 prefixEnd_25785 871776044529175293427 := by
  unfold tailWord_25785
  simp only [CollatzResearch.WordTrace]
  refine ⟨940456211592823572510809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 626970807728549048340539 940456211592823572510809)
  ·
    refine ⟨705342158694617679383107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 940456211592823572510809 705342158694617679383107)
    ·
      refine ⟨1058013238041926519074661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 705342158694617679383107 1058013238041926519074661)
      ·
        refine ⟨198377482132861222326499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1058013238041926519074661 198377482132861222326499)
        ·
          refine ⟨297566223199291833489749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198377482132861222326499 297566223199291833489749)
          ·
            refine ⟨871776044529175293427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 297566223199291833489749 871776044529175293427)
            ·
              rfl

theorem cell19_25785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 10].length) (baseStart_25785 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_25785 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_25785 prefixEnd_25785 := by exact prefixLift 25785
  have htrace : WordTrace (prefixWord ++ tailWord_25785) baseStart_25785 baseEnd_25785 := by
    simpa [prefixWord, tailWord_25785, baseEnd_25785] using wordTrace_append hprefix tailTrace_25785
  have hstable : (prefixWord ++ tailWord_25785).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25785).length < 2 ^ (prefixWord ++ tailWord_25785).sum := by decide
  have hdescent : baseEnd_25785 < baseStart_25785 := by decide
  rcases family_descends (prefixWord ++ tailWord_25785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25794 : List Nat := [3, 5, 1, 1, 3, 1, 1, 4]
def baseStart_25794 : Nat := 118140960795 + 25794 * 2 ^ 59
def prefixEnd_25794 : Nat := 4983230072969 + 3 ^ 40 * 25794 * 2
def baseEnd_25794 : Nat := 7848722964253223440819

theorem tailTrace_25794 : CollatzResearch.WordTrace tailWord_25794 prefixEnd_25794 7848722964253223440819 := by
  unfold tailWord_25794
  simp only [CollatzResearch.WordTrace]
  refine ⟨235196117140054527397109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 627189645706812073058957 235196117140054527397109)
  ·
    refine ⟨22049635981880111943479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 235196117140054527397109 22049635981880111943479)
    ·
      refine ⟨33074453972820167915219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22049635981880111943479 33074453972820167915219)
      ·
        refine ⟨49611680959230251872829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33074453972820167915219 49611680959230251872829)
        ·
          refine ⟨18604380359711344452311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49611680959230251872829 18604380359711344452311)
          ·
            refine ⟨27906570539567016678467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18604380359711344452311 27906570539567016678467)
            ·
              refine ⟨41859855809350525017701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27906570539567016678467 41859855809350525017701)
              ·
                refine ⟨7848722964253223440819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41859855809350525017701 7848722964253223440819)
                ·
                  rfl

theorem cell19_25794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 4].length) (baseStart_25794 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_25794 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_25794 prefixEnd_25794 := by exact prefixLift 25794
  have htrace : WordTrace (prefixWord ++ tailWord_25794) baseStart_25794 baseEnd_25794 := by
    simpa [prefixWord, tailWord_25794, baseEnd_25794] using wordTrace_append hprefix tailTrace_25794
  have hstable : (prefixWord ++ tailWord_25794).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25794).length < 2 ^ (prefixWord ++ tailWord_25794).sum := by decide
  have hdescent : baseEnd_25794 < baseStart_25794 := by decide
  rcases family_descends (prefixWord ++ tailWord_25794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25802 : List Nat := [3, 1, 2, 1, 3, 2, 3, 4]
def baseStart_25802 : Nat := 118140960795 + 25802 * 2 ^ 59
def prefixEnd_25802 : Nat := 4983230072969 + 3 ^ 40 * 25802 * 2
def baseEnd_25802 : Nat := 7851157242911575263019

theorem tailTrace_25802 : CollatzResearch.WordTrace tailWord_25802 prefixEnd_25802 7851157242911575263019 := by
  unfold tailWord_25802
  simp only [CollatzResearch.WordTrace]
  refine ⟨235269063132808868969915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 627384168354156983919773 235269063132808868969915)
  ·
    refine ⟨352903594699213303454873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235269063132808868969915 352903594699213303454873)
    ·
      refine ⟨264677696024409977591155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 352903594699213303454873 264677696024409977591155)
      ·
        refine ⟨397016544036614966386733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264677696024409977591155 397016544036614966386733)
        ·
          refine ⟨148881204013730612395025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 397016544036614966386733 148881204013730612395025)
          ·
            refine ⟨111660903010297959296269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148881204013730612395025 111660903010297959296269)
            ·
              refine ⟨41872838628861734736101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111660903010297959296269 41872838628861734736101)
              ·
                refine ⟨7851157242911575263019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41872838628861734736101 7851157242911575263019)
                ·
                  rfl

theorem cell19_25802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_25802 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_25802 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_25802 prefixEnd_25802 := by exact prefixLift 25802
  have htrace : WordTrace (prefixWord ++ tailWord_25802) baseStart_25802 baseEnd_25802 := by
    simpa [prefixWord, tailWord_25802, baseEnd_25802] using wordTrace_append hprefix tailTrace_25802
  have hstable : (prefixWord ++ tailWord_25802).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25802).length < 2 ^ (prefixWord ++ tailWord_25802).sum := by decide
  have hdescent : baseEnd_25802 < baseStart_25802 := by decide
  rcases family_descends (prefixWord ++ tailWord_25802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25823 : List Nat := [1, 1, 2, 3, 2, 1, 2, 7]
def baseStart_25823 : Nat := 118140960795 + 25823 * 2 ^ 59
def prefixEnd_25823 : Nat := 4983230072969 + 3 ^ 40 * 25823 * 2
def baseEnd_25823 : Nat := 7857547224389748796295

theorem tailTrace_25823 : CollatzResearch.WordTrace tailWord_25823 prefixEnd_25823 7857547224389748796295 := by
  unfold tailWord_25823
  simp only [CollatzResearch.WordTrace]
  refine ⟨941842185455156062394123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 627894790303437374929415 941842185455156062394123)
  ·
    refine ⟨1412763278182734093591185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 941842185455156062394123 1412763278182734093591185)
    ·
      refine ⟨1059572458637050570193389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1412763278182734093591185 1059572458637050570193389)
      ·
        refine ⟨397339671988893963822521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1059572458637050570193389 397339671988893963822521)
        ·
          refine ⟨298004753991670472866891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 397339671988893963822521 298004753991670472866891)
          ·
            refine ⟨447007130987505709300337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298004753991670472866891 447007130987505709300337)
            ·
              refine ⟨335255348240629281975253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 447007130987505709300337 335255348240629281975253)
              ·
                refine ⟨7857547224389748796295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 335255348240629281975253 7857547224389748796295)
                ·
                  rfl

theorem cell19_25823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 7].length) (baseStart_25823 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_25823 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_25823 prefixEnd_25823 := by exact prefixLift 25823
  have htrace : WordTrace (prefixWord ++ tailWord_25823) baseStart_25823 baseEnd_25823 := by
    simpa [prefixWord, tailWord_25823, baseEnd_25823] using wordTrace_append hprefix tailTrace_25823
  have hstable : (prefixWord ++ tailWord_25823).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25823).length < 2 ^ (prefixWord ++ tailWord_25823).sum := by decide
  have hdescent : baseEnd_25823 < baseStart_25823 := by decide
  rcases family_descends (prefixWord ++ tailWord_25823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25861 : List Nat := [1, 3, 1, 1, 2, 1, 4, 6]
def baseStart_25861 : Nat := 118140960795 + 25861 * 2 ^ 59
def prefixEnd_25861 : Nat := 4983230072969 + 3 ^ 40 * 25861 * 2
def baseEnd_25861 : Nat := 7869110048016919951747

theorem tailTrace_25861 : CollatzResearch.WordTrace tailWord_25861 prefixEnd_25861 7869110048016919951747 := by
  unfold tailWord_25861
  simp only [CollatzResearch.WordTrace]
  refine ⟨943228159317488552277437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 628818772878325701518291 943228159317488552277437)
  ·
    refine ⟨353710559744058207104039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 943228159317488552277437 353710559744058207104039)
    ·
      refine ⟨530565839616087310656059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353710559744058207104039 530565839616087310656059)
      ·
        refine ⟨795848759424130965984089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 530565839616087310656059 795848759424130965984089)
        ·
          refine ⟨596886569568098224488067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 795848759424130965984089 596886569568098224488067)
          ·
            refine ⟨895329854352147336732101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 596886569568098224488067 895329854352147336732101)
            ·
              refine ⟨167874347691027625637269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 895329854352147336732101 167874347691027625637269)
              ·
                refine ⟨7869110048016919951747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 167874347691027625637269 7869110048016919951747)
                ·
                  rfl

theorem cell19_25861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 6].length) (baseStart_25861 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_25861 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_25861 prefixEnd_25861 := by exact prefixLift 25861
  have htrace : WordTrace (prefixWord ++ tailWord_25861) baseStart_25861 baseEnd_25861 := by
    simpa [prefixWord, tailWord_25861, baseEnd_25861] using wordTrace_append hprefix tailTrace_25861
  have hstable : (prefixWord ++ tailWord_25861).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25861).length < 2 ^ (prefixWord ++ tailWord_25861).sum := by decide
  have hdescent : baseEnd_25861 < baseStart_25861 := by decide
  rcases family_descends (prefixWord ++ tailWord_25861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25874 : List Nat := [3, 2, 4, 2, 1, 1, 1, 5]
def baseStart_25874 : Nat := 118140960795 + 25874 * 2 ^ 59
def prefixEnd_25874 : Nat := 4983230072969 + 3 ^ 40 * 25874 * 2
def baseEnd_25874 : Nat := 7873065750836741662823

theorem tailTrace_25874 : CollatzResearch.WordTrace tailWord_25874 prefixEnd_25874 7873065750836741662823 := by
  unfold tailWord_25874
  simp only [CollatzResearch.WordTrace]
  refine ⟨235925577067597943125169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 629134872180261181667117 235925577067597943125169)
  ·
    refine ⟨176944182800698457343877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235925577067597943125169 176944182800698457343877)
    ·
      refine ⟨33177034275130960751977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176944182800698457343877 33177034275130960751977)
      ·
        refine ⟨24882775706348220563983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33177034275130960751977 24882775706348220563983)
        ·
          refine ⟨37324163559522330845975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24882775706348220563983 37324163559522330845975)
          ·
            refine ⟨55986245339283496268963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37324163559522330845975 55986245339283496268963)
            ·
              refine ⟨83979368008925244403445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55986245339283496268963 83979368008925244403445)
              ·
                refine ⟨7873065750836741662823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83979368008925244403445 7873065750836741662823)
                ·
                  rfl

theorem cell19_25874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 5].length) (baseStart_25874 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_25874 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_25874 prefixEnd_25874 := by exact prefixLift 25874
  have htrace : WordTrace (prefixWord ++ tailWord_25874) baseStart_25874 baseEnd_25874 := by
    simpa [prefixWord, tailWord_25874, baseEnd_25874] using wordTrace_append hprefix tailTrace_25874
  have hstable : (prefixWord ++ tailWord_25874).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25874).length < 2 ^ (prefixWord ++ tailWord_25874).sum := by decide
  have hdescent : baseEnd_25874 < baseStart_25874 := by decide
  rcases family_descends (prefixWord ++ tailWord_25874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25916 : List Nat := [2, 2, 2, 2, 1, 4, 2, 4]
def baseStart_25916 : Nat := 118140960795 + 25916 * 2 ^ 59
def prefixEnd_25916 : Nat := 4983230072969 + 3 ^ 40 * 25916 * 2
def baseEnd_25916 : Nat := 7885845713793088729375

theorem tailTrace_25916 : CollatzResearch.WordTrace tailWord_25916 prefixEnd_25916 7885845713793088729375 := by
  unfold tailWord_25916
  simp only [CollatzResearch.WordTrace]
  refine ⟨472617087059116472764801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 630156116078821963686401 472617087059116472764801)
  ·
    refine ⟨354462815294337354573601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 472617087059116472764801 354462815294337354573601)
    ·
      refine ⟨265847111470753015930201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 354462815294337354573601 265847111470753015930201)
      ·
        refine ⟨199385333603064761947651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265847111470753015930201 199385333603064761947651)
        ·
          refine ⟨299078000404597142921477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199385333603064761947651 299078000404597142921477)
          ·
            refine ⟨56077125075861964297777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 299078000404597142921477 56077125075861964297777)
            ·
              refine ⟨42057843806896473223333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56077125075861964297777 42057843806896473223333)
              ·
                refine ⟨7885845713793088729375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42057843806896473223333 7885845713793088729375)
                ·
                  rfl

theorem cell19_25916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 4].length) (baseStart_25916 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_25916 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_25916 prefixEnd_25916 := by exact prefixLift 25916
  have htrace : WordTrace (prefixWord ++ tailWord_25916) baseStart_25916 baseEnd_25916 := by
    simpa [prefixWord, tailWord_25916, baseEnd_25916] using wordTrace_append hprefix tailTrace_25916
  have hstable : (prefixWord ++ tailWord_25916).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25916).length < 2 ^ (prefixWord ++ tailWord_25916).sum := by decide
  have hdescent : baseEnd_25916 < baseStart_25916 := by decide
  rcases family_descends (prefixWord ++ tailWord_25916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25937 : List Nat := [1, 2, 2, 1, 4, 1, 1, 7]
def baseStart_25937 : Nat := 118140960795 + 25937 * 2 ^ 59
def prefixEnd_25937 : Nat := 4983230072969 + 3 ^ 40 * 25937 * 2
def baseEnd_25937 : Nat := 7892235695271262262651

theorem tailTrace_25937 : CollatzResearch.WordTrace tailWord_25937 prefixEnd_25937 7892235695271262262651 := by
  unfold tailWord_25937
  simp only [CollatzResearch.WordTrace]
  refine ⟨946000107042153532044065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 630666738028102354696043 946000107042153532044065)
  ·
    refine ⟨709500080281615149033049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 946000107042153532044065 709500080281615149033049)
    ·
      refine ⟨532125060211211361774787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 709500080281615149033049 532125060211211361774787)
      ·
        refine ⟨798187590316817042662181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 532125060211211361774787 798187590316817042662181)
        ·
          refine ⟨149660173184403195499159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 798187590316817042662181 149660173184403195499159)
          ·
            refine ⟨224490259776604793248739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149660173184403195499159 224490259776604793248739)
            ·
              refine ⟨336735389664907189873109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224490259776604793248739 336735389664907189873109)
              ·
                refine ⟨7892235695271262262651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 336735389664907189873109 7892235695271262262651)
                ·
                  rfl

theorem cell19_25937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 7].length) (baseStart_25937 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_25937 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_25937 prefixEnd_25937 := by exact prefixLift 25937
  have htrace : WordTrace (prefixWord ++ tailWord_25937) baseStart_25937 baseEnd_25937 := by
    simpa [prefixWord, tailWord_25937, baseEnd_25937] using wordTrace_append hprefix tailTrace_25937
  have hstable : (prefixWord ++ tailWord_25937).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25937).length < 2 ^ (prefixWord ++ tailWord_25937).sum := by decide
  have hdescent : baseEnd_25937 < baseStart_25937 := by decide
  rcases family_descends (prefixWord ++ tailWord_25937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25956 : List Nat := [2, 3, 1, 1, 3, 9]
def baseStart_25956 : Nat := 118140960795 + 25956 * 2 ^ 59
def prefixEnd_25956 : Nat := 4983230072969 + 3 ^ 40 * 25956 * 2
def baseEnd_25956 : Nat := 877557456342760871153

theorem tailTrace_25956 : CollatzResearch.WordTrace tailWord_25956 prefixEnd_25956 877557456342760871153 := by
  unfold tailWord_25956
  simp only [CollatzResearch.WordTrace]
  refine ⟨473346546986659888492861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 631128729315546517990481 473346546986659888492861)
  ·
    refine ⟨177504955119997458184823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 473346546986659888492861 177504955119997458184823)
    ·
      refine ⟨266257432679996187277235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177504955119997458184823 266257432679996187277235)
      ·
        refine ⟨399386149019994280915853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266257432679996187277235 399386149019994280915853)
        ·
          refine ⟨149769805882497855343445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 399386149019994280915853 149769805882497855343445)
          ·
            refine ⟨877557456342760871153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 149769805882497855343445 877557456342760871153)
            ·
              rfl

theorem cell19_25956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 9].length) (baseStart_25956 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_25956 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_25956 prefixEnd_25956 := by exact prefixLift 25956
  have htrace : WordTrace (prefixWord ++ tailWord_25956) baseStart_25956 baseEnd_25956 := by
    simpa [prefixWord, tailWord_25956, baseEnd_25956] using wordTrace_append hprefix tailTrace_25956
  have hstable : (prefixWord ++ tailWord_25956).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25956).length < 2 ^ (prefixWord ++ tailWord_25956).sum := by decide
  have hdescent : baseEnd_25956 < baseStart_25956 := by decide
  rcases family_descends (prefixWord ++ tailWord_25956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26087 : List Nat := [1, 1, 5, 2, 1, 3, 2, 4]
def baseStart_26087 : Nat := 118140960795 + 26087 * 2 ^ 59
def prefixEnd_26087 : Nat := 4983230072969 + 3 ^ 40 * 26087 * 2
def baseEnd_26087 : Nat := 7937878420115358928909

theorem tailTrace_26087 : CollatzResearch.WordTrace tailWord_26087 prefixEnd_26087 7937878420115358928909 := by
  unfold tailWord_26087
  simp only [CollatzResearch.WordTrace]
  refine ⟨951471056498729150004515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 634314037665819433336343 951471056498729150004515)
  ·
    refine ⟨1427206584748093725006773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 951471056498729150004515 1427206584748093725006773)
    ·
      refine ⟨133800617320133786719385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1427206584748093725006773 133800617320133786719385)
      ·
        refine ⟨100350462990100340039539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133800617320133786719385 100350462990100340039539)
        ·
          refine ⟨150525694485150510059309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100350462990100340039539 150525694485150510059309)
          ·
            refine ⟨56447135431931441272241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150525694485150510059309 56447135431931441272241)
            ·
              refine ⟨42335351573948580954181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56447135431931441272241 42335351573948580954181)
              ·
                refine ⟨7937878420115358928909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42335351573948580954181 7937878420115358928909)
                ·
                  rfl

theorem cell19_26087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 4].length) (baseStart_26087 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_26087 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_26087 prefixEnd_26087 := by exact prefixLift 26087
  have htrace : WordTrace (prefixWord ++ tailWord_26087) baseStart_26087 baseEnd_26087 := by
    simpa [prefixWord, tailWord_26087, baseEnd_26087] using wordTrace_append hprefix tailTrace_26087
  have hstable : (prefixWord ++ tailWord_26087).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26087).length < 2 ^ (prefixWord ++ tailWord_26087).sum := by decide
  have hdescent : baseEnd_26087 < baseStart_26087 := by decide
  rcases family_descends (prefixWord ++ tailWord_26087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26108 : List Nat := [2, 2, 2, 1, 2, 1, 4, 5]
def baseStart_26108 : Nat := 118140960795 + 26108 * 2 ^ 59
def prefixEnd_26108 : Nat := 4983230072969 + 3 ^ 40 * 26108 * 2
def baseEnd_26108 : Nat := 7944268401593532462185

theorem tailTrace_26108 : CollatzResearch.WordTrace tailWord_26108 prefixEnd_26108 7944268401593532462185 := by
  unfold tailWord_26108
  simp only [CollatzResearch.WordTrace]
  refine ⟨476118494711324868259489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 634824659615099824345985 476118494711324868259489)
  ·
    refine ⟨357088871033493651194617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 476118494711324868259489 357088871033493651194617)
    ·
      refine ⟨267816653275120238395963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357088871033493651194617 267816653275120238395963)
      ·
        refine ⟨401724979912680357593945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267816653275120238395963 401724979912680357593945)
        ·
          refine ⟨301293734934510268195459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 401724979912680357593945 301293734934510268195459)
          ·
            refine ⟨451940602401765402293189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301293734934510268195459 451940602401765402293189)
            ·
              refine ⟨84738862950331012929973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 451940602401765402293189 84738862950331012929973)
              ·
                refine ⟨7944268401593532462185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84738862950331012929973 7944268401593532462185)
                ·
                  rfl

theorem cell19_26108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 5].length) (baseStart_26108 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_26108 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_26108 prefixEnd_26108 := by exact prefixLift 26108
  have htrace : WordTrace (prefixWord ++ tailWord_26108) baseStart_26108 baseEnd_26108 := by
    simpa [prefixWord, tailWord_26108, baseEnd_26108] using wordTrace_append hprefix tailTrace_26108
  have hstable : (prefixWord ++ tailWord_26108).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26108).length < 2 ^ (prefixWord ++ tailWord_26108).sum := by decide
  have hdescent : baseEnd_26108 < baseStart_26108 := by decide
  rcases family_descends (prefixWord ++ tailWord_26108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26144 : List Nat := [2, 1, 1, 6, 1, 1, 3, 4]
def baseStart_26144 : Nat := 118140960795 + 26144 * 2 ^ 59
def prefixEnd_26144 : Nat := 4983230072969 + 3 ^ 40 * 26144 * 2
def baseEnd_26144 : Nat := 7955222655556115662087

theorem tailTrace_26144 : CollatzResearch.WordTrace tailWord_26144 prefixEnd_26144 7955222655556115662087 := by
  unfold tailWord_26144
  simp only [CollatzResearch.WordTrace]
  refine ⟨476775008646113942414743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 635700011528151923219657 476775008646113942414743)
  ·
    refine ⟨715162512969170913622115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 476775008646113942414743 715162512969170913622115)
    ·
      refine ⟨1072743769453756370433173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 715162512969170913622115 1072743769453756370433173)
      ·
        refine ⟨50284864193144829864055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1072743769453756370433173 50284864193144829864055)
        ·
          refine ⟨75427296289717244796083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50284864193144829864055 75427296289717244796083)
          ·
            refine ⟨113140944434575867194125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75427296289717244796083 113140944434575867194125)
            ·
              refine ⟨42427854162965950197797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113140944434575867194125 42427854162965950197797)
              ·
                refine ⟨7955222655556115662087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42427854162965950197797 7955222655556115662087)
                ·
                  rfl

theorem cell19_26144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 4].length) (baseStart_26144 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_26144 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_26144 prefixEnd_26144 := by exact prefixLift 26144
  have htrace : WordTrace (prefixWord ++ tailWord_26144) baseStart_26144 baseEnd_26144 := by
    simpa [prefixWord, tailWord_26144, baseEnd_26144] using wordTrace_append hprefix tailTrace_26144
  have hstable : (prefixWord ++ tailWord_26144).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26144).length < 2 ^ (prefixWord ++ tailWord_26144).sum := by decide
  have hdescent : baseEnd_26144 < baseStart_26144 := by decide
  rcases family_descends (prefixWord ++ tailWord_26144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26163 : List Nat := [1, 1, 1, 2, 4, 4, 3, 3]
def baseStart_26163 : Nat := 118140960795 + 26163 * 2 ^ 59
def prefixEnd_26163 : Nat := 4983230072969 + 3 ^ 40 * 26163 * 2
def baseEnd_26163 : Nat := 7961004067369701239813

theorem tailTrace_26163 : CollatzResearch.WordTrace tailWord_26163 prefixEnd_26163 7961004067369701239813 := by
  unfold tailWord_26163
  simp only [CollatzResearch.WordTrace]
  refine ⟨954243004223394129771143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 636162002815596086514095 954243004223394129771143)
  ·
    refine ⟨1431364506335091194656715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 954243004223394129771143 1431364506335091194656715)
    ·
      refine ⟨2147046759502636791985073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1431364506335091194656715 2147046759502636791985073)
      ·
        refine ⟨1610285069626977593988805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2147046759502636791985073 1610285069626977593988805)
        ·
          refine ⟨301928450555058298872901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1610285069626977593988805 301928450555058298872901)
          ·
            refine ⟨56611584479073431038669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 301928450555058298872901 56611584479073431038669)
            ·
              refine ⟨21229344179652536639501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56611584479073431038669 21229344179652536639501)
              ·
                refine ⟨7961004067369701239813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21229344179652536639501 7961004067369701239813)
                ·
                  rfl

theorem cell19_26163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 3].length) (baseStart_26163 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_26163 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_26163 prefixEnd_26163 := by exact prefixLift 26163
  have htrace : WordTrace (prefixWord ++ tailWord_26163) baseStart_26163 baseEnd_26163 := by
    simpa [prefixWord, tailWord_26163, baseEnd_26163] using wordTrace_append hprefix tailTrace_26163
  have hstable : (prefixWord ++ tailWord_26163).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26163).length < 2 ^ (prefixWord ++ tailWord_26163).sum := by decide
  have hdescent : baseEnd_26163 < baseStart_26163 := by decide
  rcases family_descends (prefixWord ++ tailWord_26163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26218 : List Nat := [3, 1, 3, 2, 1, 4, 2, 3]
def baseStart_26218 : Nat := 118140960795 + 26218 * 2 ^ 59
def prefixEnd_26218 : Nat := 4983230072969 + 3 ^ 40 * 26218 * 2
def baseEnd_26218 : Nat := 7977739733145870017441

theorem tailTrace_26218 : CollatzResearch.WordTrace tailWord_26218 prefixEnd_26218 7977739733145870017441 := by
  unfold tailWord_26218
  simp only [CollatzResearch.WordTrace]
  refine ⟨239062254756034630755827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 637499346016092348682205 239062254756034630755827)
  ·
    refine ⟨358593382134051946133741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239062254756034630755827 358593382134051946133741)
    ·
      refine ⟨134472518300269479800153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 358593382134051946133741 134472518300269479800153)
      ·
        refine ⟨100854388725202109850115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134472518300269479800153 100854388725202109850115)
        ·
          refine ⟨151281583087803164775173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100854388725202109850115 151281583087803164775173)
          ·
            refine ⟨28365296828963093395345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 151281583087803164775173 28365296828963093395345)
            ·
              refine ⟨21273972621722320046509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28365296828963093395345 21273972621722320046509)
              ·
                refine ⟨7977739733145870017441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21273972621722320046509 7977739733145870017441)
                ·
                  rfl

theorem cell19_26218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 3].length) (baseStart_26218 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_26218 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_26218 prefixEnd_26218 := by exact prefixLift 26218
  have htrace : WordTrace (prefixWord ++ tailWord_26218) baseStart_26218 baseEnd_26218 := by
    simpa [prefixWord, tailWord_26218, baseEnd_26218] using wordTrace_append hprefix tailTrace_26218
  have hstable : (prefixWord ++ tailWord_26218).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26218).length < 2 ^ (prefixWord ++ tailWord_26218).sum := by decide
  have hdescent : baseEnd_26218 < baseStart_26218 := by decide
  rcases family_descends (prefixWord ++ tailWord_26218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26241 : List Nat := [1, 2, 4, 2, 1, 2, 7]
def baseStart_26241 : Nat := 118140960795 + 26241 * 2 ^ 59
def prefixEnd_26241 : Nat := 4983230072969 + 3 ^ 40 * 26241 * 2
def baseEnd_26241 : Nat := 2661579428096210502089

theorem tailTrace_26241 : CollatzResearch.WordTrace tailWord_26241 prefixEnd_26241 2661579428096210502089 := by
  unfold tailWord_26241
  simp only [CollatzResearch.WordTrace]
  refine ⟨957087897940813451110577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 638058598627208967407051 957087897940813451110577)
  ·
    refine ⟨717815923455610088332933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 957087897940813451110577 717815923455610088332933)
    ·
      refine ⟨134590485647926891562425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 717815923455610088332933 134590485647926891562425)
      ·
        refine ⟨100942864235945168671819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134590485647926891562425 100942864235945168671819)
        ·
          refine ⟨151414296353917753007729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100942864235945168671819 151414296353917753007729)
          ·
            refine ⟨113560722265438314755797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151414296353917753007729 113560722265438314755797)
            ·
              refine ⟨2661579428096210502089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 113560722265438314755797 2661579428096210502089)
              ·
                rfl

theorem cell19_26241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 7].length) (baseStart_26241 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_26241 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_26241 prefixEnd_26241 := by exact prefixLift 26241
  have htrace : WordTrace (prefixWord ++ tailWord_26241) baseStart_26241 baseEnd_26241 := by
    simpa [prefixWord, tailWord_26241, baseEnd_26241] using wordTrace_append hprefix tailTrace_26241
  have hstable : (prefixWord ++ tailWord_26241).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26241).length < 2 ^ (prefixWord ++ tailWord_26241).sum := by decide
  have hdescent : baseEnd_26241 < baseStart_26241 := by decide
  rcases family_descends (prefixWord ++ tailWord_26241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26381 : List Nat := [1, 7, 2, 1, 2, 1, 2, 3]
def baseStart_26381 : Nat := 118140960795 + 26381 * 2 ^ 59
def prefixEnd_26381 : Nat := 4983230072969 + 3 ^ 40 * 26381 * 2
def baseEnd_26381 : Nat := 8027338160809788394775

theorem tailTrace_26381 : CollatzResearch.WordTrace tailWord_26381 prefixEnd_26381 8027338160809788394775 := by
  unfold tailWord_26381
  simp only [CollatzResearch.WordTrace]
  refine ⟨962194117433617361206997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 641462744955744907471331 962194117433617361206997)
  ·
    refine ⟨22551424627350406903289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 962194117433617361206997 22551424627350406903289)
    ·
      refine ⟨16913568470512805177467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22551424627350406903289 16913568470512805177467)
      ·
        refine ⟨25370352705769207766201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16913568470512805177467 25370352705769207766201)
        ·
          refine ⟨19027764529326905824651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25370352705769207766201 19027764529326905824651)
          ·
            refine ⟨28541646793990358736977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19027764529326905824651 28541646793990358736977)
            ·
              refine ⟨21406235095492769052733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28541646793990358736977 21406235095492769052733)
              ·
                refine ⟨8027338160809788394775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21406235095492769052733 8027338160809788394775)
                ·
                  rfl

theorem cell19_26381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 3].length) (baseStart_26381 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_26381 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_26381 prefixEnd_26381 := by exact prefixLift 26381
  have htrace : WordTrace (prefixWord ++ tailWord_26381) baseStart_26381 baseEnd_26381 := by
    simpa [prefixWord, tailWord_26381, baseEnd_26381] using wordTrace_append hprefix tailTrace_26381
  have hstable : (prefixWord ++ tailWord_26381).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26381).length < 2 ^ (prefixWord ++ tailWord_26381).sum := by decide
  have hdescent : baseEnd_26381 < baseStart_26381 := by decide
  rcases family_descends (prefixWord ++ tailWord_26381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26391 : List Nat := [1, 1, 3, 4, 2, 1, 4, 3]
def baseStart_26391 : Nat := 118140960795 + 26391 * 2 ^ 59
def prefixEnd_26391 : Nat := 4983230072969 + 3 ^ 40 * 26391 * 2
def baseEnd_26391 : Nat := 8030381009132728172525

theorem tailTrace_26391 : CollatzResearch.WordTrace tailWord_26391 prefixEnd_26391 8030381009132728172525 := by
  unfold tailWord_26391
  simp only [CollatzResearch.WordTrace]
  refine ⟨962558847397389069071027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 641705898264926046047351 962558847397389069071027)
  ·
    refine ⟨1443838271096083603606541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 962558847397389069071027 1443838271096083603606541)
    ·
      refine ⟨541439351661031351352453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1443838271096083603606541 541439351661031351352453)
      ·
        refine ⟨101519878436443378378585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 541439351661031351352453 101519878436443378378585)
        ·
          refine ⟨76139908827332533783939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101519878436443378378585 76139908827332533783939)
          ·
            refine ⟨114209863240998800675909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76139908827332533783939 114209863240998800675909)
            ·
              refine ⟨21414349357687275126733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114209863240998800675909 21414349357687275126733)
              ·
                refine ⟨8030381009132728172525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21414349357687275126733 8030381009132728172525)
                ·
                  rfl

theorem cell19_26391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 3].length) (baseStart_26391 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_26391 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_26391 prefixEnd_26391 := by exact prefixLift 26391
  have htrace : WordTrace (prefixWord ++ tailWord_26391) baseStart_26391 baseEnd_26391 := by
    simpa [prefixWord, tailWord_26391, baseEnd_26391] using wordTrace_append hprefix tailTrace_26391
  have hstable : (prefixWord ++ tailWord_26391).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26391).length < 2 ^ (prefixWord ++ tailWord_26391).sum := by decide
  have hdescent : baseEnd_26391 < baseStart_26391 := by decide
  rcases family_descends (prefixWord ++ tailWord_26391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26395 : List Nat := [1, 1, 1, 1, 1, 1, 4, 9]
def baseStart_26395 : Nat := 118140960795 + 26395 * 2 ^ 59
def prefixEnd_26395 : Nat := 4983230072969 + 3 ^ 40 * 26395 * 2
def baseEnd_26395 : Nat := 8031598148461904083625

theorem tailTrace_26395 : CollatzResearch.WordTrace tailWord_26395 prefixEnd_26395 8031598148461904083625 := by
  unfold tailWord_26395
  simp only [CollatzResearch.WordTrace]
  refine ⟨962704739382897752216639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 641803159588598501477759 962704739382897752216639)
  ·
    refine ⟨1444057109074346628324959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 962704739382897752216639 1444057109074346628324959)
    ·
      refine ⟨2166085663611519942487439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1444057109074346628324959 2166085663611519942487439)
      ·
        refine ⟨3249128495417279913731159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2166085663611519942487439 3249128495417279913731159)
        ·
          refine ⟨4873692743125919870596739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3249128495417279913731159 4873692743125919870596739)
          ·
            refine ⟨7310539114688879805895109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4873692743125919870596739 7310539114688879805895109)
            ·
              refine ⟨1370726084004164963605333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7310539114688879805895109 1370726084004164963605333)
              ·
                refine ⟨8031598148461904083625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1370726084004164963605333 8031598148461904083625)
                ·
                  rfl

theorem cell19_26395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 9].length) (baseStart_26395 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_26395 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_26395 prefixEnd_26395 := by exact prefixLift 26395
  have htrace : WordTrace (prefixWord ++ tailWord_26395) baseStart_26395 baseEnd_26395 := by
    simpa [prefixWord, tailWord_26395, baseEnd_26395] using wordTrace_append hprefix tailTrace_26395
  have hstable : (prefixWord ++ tailWord_26395).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26395).length < 2 ^ (prefixWord ++ tailWord_26395).sum := by decide
  have hdescent : baseEnd_26395 < baseStart_26395 := by decide
  rcases family_descends (prefixWord ++ tailWord_26395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26412 : List Nat := [2, 2, 1, 1, 1, 7, 5]
def baseStart_26412 : Nat := 118140960795 + 26412 * 2 ^ 59
def prefixEnd_26412 : Nat := 4983230072969 + 3 ^ 40 * 26412 * 2
def baseEnd_26412 : Nat := 2678923663536967235267

theorem tailTrace_26412 : CollatzResearch.WordTrace tailWord_26412 prefixEnd_26412 2678923663536967235267 := by
  unfold tailWord_26412
  simp only [CollatzResearch.WordTrace]
  refine ⟨481662390160654827792745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 642216520214206437056993 481662390160654827792745)
  ·
    refine ⟨361246792620491120844559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 481662390160654827792745 361246792620491120844559)
    ·
      refine ⟨541870188930736681266839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361246792620491120844559 541870188930736681266839)
      ·
        refine ⟨812805283396105021900259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 541870188930736681266839 812805283396105021900259)
        ·
          refine ⟨1219207925094157532850389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 812805283396105021900259 1219207925094157532850389)
          ·
            refine ⟨28575185744394317176181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1219207925094157532850389 28575185744394317176181)
            ·
              refine ⟨2678923663536967235267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28575185744394317176181 2678923663536967235267)
              ·
                rfl

theorem cell19_26412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 5].length) (baseStart_26412 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_26412 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_26412 prefixEnd_26412 := by exact prefixLift 26412
  have htrace : WordTrace (prefixWord ++ tailWord_26412) baseStart_26412 baseEnd_26412 := by
    simpa [prefixWord, tailWord_26412, baseEnd_26412] using wordTrace_append hprefix tailTrace_26412
  have hstable : (prefixWord ++ tailWord_26412).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26412).length < 2 ^ (prefixWord ++ tailWord_26412).sum := by decide
  have hdescent : baseEnd_26412 < baseStart_26412 := by decide
  rcases family_descends (prefixWord ++ tailWord_26412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26429 : List Nat := [1, 4, 1, 4, 1, 2, 2, 4]
def baseStart_26429 : Nat := 118140960795 + 26429 * 2 ^ 59
def prefixEnd_26429 : Nat := 4983230072969 + 3 ^ 40 * 26429 * 2
def baseEnd_26429 : Nat := 8041943832759899327977

theorem tailTrace_26429 : CollatzResearch.WordTrace tailWord_26429 prefixEnd_26429 8041943832759899327977 := by
  unfold tailWord_26429
  simp only [CollatzResearch.WordTrace]
  refine ⟨963944821259721558954341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 642629880839814372636227 963944821259721558954341)
  ·
    refine ⟨180739653986197792303939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 963944821259721558954341 180739653986197792303939)
    ·
      refine ⟨271109480979296688455909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180739653986197792303939 271109480979296688455909)
      ·
        refine ⟨50833027683618129085483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 271109480979296688455909 50833027683618129085483)
        ·
          refine ⟨76249541525427193628225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50833027683618129085483 76249541525427193628225)
          ·
            refine ⟨57187156144070395221169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76249541525427193628225 57187156144070395221169)
            ·
              refine ⟨42890367108052796415877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57187156144070395221169 42890367108052796415877)
              ·
                refine ⟨8041943832759899327977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42890367108052796415877 8041943832759899327977)
                ·
                  rfl

theorem cell19_26429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 4].length) (baseStart_26429 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_26429 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_26429 prefixEnd_26429 := by exact prefixLift 26429
  have htrace : WordTrace (prefixWord ++ tailWord_26429) baseStart_26429 baseEnd_26429 := by
    simpa [prefixWord, tailWord_26429, baseEnd_26429] using wordTrace_append hprefix tailTrace_26429
  have hstable : (prefixWord ++ tailWord_26429).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26429).length < 2 ^ (prefixWord ++ tailWord_26429).sum := by decide
  have hdescent : baseEnd_26429 < baseStart_26429 := by decide
  rcases family_descends (prefixWord ++ tailWord_26429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26450 : List Nat := [3, 2, 2, 1, 1, 3, 2, 5]
def baseStart_26450 : Nat := 118140960795 + 26450 * 2 ^ 59
def prefixEnd_26450 : Nat := 4983230072969 + 3 ^ 40 * 26450 * 2
def baseEnd_26450 : Nat := 8048333814238072861253

theorem tailTrace_26450 : CollatzResearch.WordTrace tailWord_26450 prefixEnd_26450 8048333814238072861253 := by
  unfold tailWord_26450
  simp only [CollatzResearch.WordTrace]
  refine ⟨241177688545910536367201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 643140502789094763645869 241177688545910536367201)
  ·
    refine ⟨180883266409432902275401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241177688545910536367201 180883266409432902275401)
    ·
      refine ⟨135662449807074676706551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180883266409432902275401 135662449807074676706551)
      ·
        refine ⟨203493674710612015059827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135662449807074676706551 203493674710612015059827)
        ·
          refine ⟨305240512065918022589741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203493674710612015059827 305240512065918022589741)
          ·
            refine ⟨114465192024719258471153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 305240512065918022589741 114465192024719258471153)
            ·
              refine ⟨85848894018539443853365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114465192024719258471153 85848894018539443853365)
              ·
                refine ⟨8048333814238072861253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85848894018539443853365 8048333814238072861253)
                ·
                  rfl

theorem cell19_26450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_26450 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_26450 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_26450 prefixEnd_26450 := by exact prefixLift 26450
  have htrace : WordTrace (prefixWord ++ tailWord_26450) baseStart_26450 baseEnd_26450 := by
    simpa [prefixWord, tailWord_26450, baseEnd_26450] using wordTrace_append hprefix tailTrace_26450
  have hstable : (prefixWord ++ tailWord_26450).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26450).length < 2 ^ (prefixWord ++ tailWord_26450).sum := by decide
  have hdescent : baseEnd_26450 < baseStart_26450 := by decide
  rcases family_descends (prefixWord ++ tailWord_26450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26547 : List Nat := [1, 1, 1, 2, 3, 1, 4, 6]
def baseStart_26547 : Nat := 118140960795 + 26547 * 2 ^ 59
def prefixEnd_26547 : Nat := 4983230072969 + 3 ^ 40 * 26547 * 2
def baseEnd_26547 : Nat := 8077849442970588705433

theorem tailTrace_26547 : CollatzResearch.WordTrace tailWord_26547 prefixEnd_26547 8077849442970588705433 := by
  unfold tailWord_26547
  simp only [CollatzResearch.WordTrace]
  refine ⟨968248634832227711749895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 645499089888151807833263 968248634832227711749895)
  ·
    refine ⟨1452372952248341567624843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 968248634832227711749895 1452372952248341567624843)
    ·
      refine ⟨2178559428372512351437265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1452372952248341567624843 2178559428372512351437265)
      ·
        refine ⟨1633919571279384263577949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2178559428372512351437265 1633919571279384263577949)
        ·
          refine ⟨612719839229769098841731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1633919571279384263577949 612719839229769098841731)
          ·
            refine ⟨919079758844653648262597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 612719839229769098841731 919079758844653648262597)
            ·
              refine ⟨172327454783372559049237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 919079758844653648262597 172327454783372559049237)
              ·
                refine ⟨8077849442970588705433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 172327454783372559049237 8077849442970588705433)
                ·
                  rfl

theorem cell19_26547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 6].length) (baseStart_26547 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_26547 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_26547 prefixEnd_26547 := by exact prefixLift 26547
  have htrace : WordTrace (prefixWord ++ tailWord_26547) baseStart_26547 baseEnd_26547 := by
    simpa [prefixWord, tailWord_26547, baseEnd_26547] using wordTrace_append hprefix tailTrace_26547
  have hstable : (prefixWord ++ tailWord_26547).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26547).length < 2 ^ (prefixWord ++ tailWord_26547).sum := by decide
  have hdescent : baseEnd_26547 < baseStart_26547 := by decide
  rcases family_descends (prefixWord ++ tailWord_26547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26602 : List Nat := [3, 1, 3, 1, 2, 1, 4, 4]
def baseStart_26602 : Nat := 118140960795 + 26602 * 2 ^ 59
def prefixEnd_26602 : Nat := 4983230072969 + 3 ^ 40 * 26602 * 2
def baseEnd_26602 : Nat := 8094585108746757483061

theorem tailTrace_26602 : CollatzResearch.WordTrace tailWord_26602 prefixEnd_26602 8094585108746757483061 := by
  unfold tailWord_26602
  simp only [CollatzResearch.WordTrace]
  refine ⟨242563662408243026250515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 646836433088648070001373 242563662408243026250515)
  ·
    refine ⟨363845493612364539375773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242563662408243026250515 363845493612364539375773)
    ·
      refine ⟨136442060104636702265915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 363845493612364539375773 136442060104636702265915)
      ·
        refine ⟨204663090156955053398873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136442060104636702265915 204663090156955053398873)
        ·
          refine ⟨153497317617716290049155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204663090156955053398873 153497317617716290049155)
          ·
            refine ⟨230245976426574435073733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153497317617716290049155 230245976426574435073733)
            ·
              refine ⟨43171120579982706576325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 230245976426574435073733 43171120579982706576325)
              ·
                refine ⟨8094585108746757483061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43171120579982706576325 8094585108746757483061)
                ·
                  rfl

theorem cell19_26602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_26602 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_26602 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_26602 prefixEnd_26602 := by exact prefixLift 26602
  have htrace : WordTrace (prefixWord ++ tailWord_26602) baseStart_26602 baseEnd_26602 := by
    simpa [prefixWord, tailWord_26602, baseEnd_26602] using wordTrace_append hprefix tailTrace_26602
  have hstable : (prefixWord ++ tailWord_26602).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26602).length < 2 ^ (prefixWord ++ tailWord_26602).sum := by decide
  have hdescent : baseEnd_26602 < baseStart_26602 := by decide
  rcases family_descends (prefixWord ++ tailWord_26602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26657 : List Nat := [1, 2, 3, 2, 4, 2, 1, 4]
def baseStart_26657 : Nat := 118140960795 + 26657 * 2 ^ 59
def prefixEnd_26657 : Nat := 4983230072969 + 3 ^ 40 * 26657 * 2
def baseEnd_26657 : Nat := 8111320774522926260689

theorem tailTrace_26657 : CollatzResearch.WordTrace tailWord_26657 prefixEnd_26657 8111320774522926260689 := by
  unfold tailWord_26657
  simp only [CollatzResearch.WordTrace]
  refine ⟨972260664433716498254225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 648173776289144332169483 972260664433716498254225)
  ·
    refine ⟨729195498325287373690669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 972260664433716498254225 729195498325287373690669)
    ·
      refine ⟨273448311871982765134001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 729195498325287373690669 273448311871982765134001)
      ·
        refine ⟨205086233903987073850501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273448311871982765134001 205086233903987073850501)
        ·
          refine ⟨38453668856997576346969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 205086233903987073850501 38453668856997576346969)
          ·
            refine ⟨28840251642748182260227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38453668856997576346969 28840251642748182260227)
            ·
              refine ⟨43260377464122273390341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28840251642748182260227 43260377464122273390341)
              ·
                refine ⟨8111320774522926260689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43260377464122273390341 8111320774522926260689)
                ·
                  rfl

theorem cell19_26657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 4].length) (baseStart_26657 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_26657 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_26657 prefixEnd_26657 := by exact prefixLift 26657
  have htrace : WordTrace (prefixWord ++ tailWord_26657) baseStart_26657 baseEnd_26657 := by
    simpa [prefixWord, tailWord_26657, baseEnd_26657] using wordTrace_append hprefix tailTrace_26657
  have hstable : (prefixWord ++ tailWord_26657).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26657).length < 2 ^ (prefixWord ++ tailWord_26657).sum := by decide
  have hdescent : baseEnd_26657 < baseStart_26657 := by decide
  rcases family_descends (prefixWord ++ tailWord_26657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26735 : List Nat := [1, 1, 2, 1, 3, 4, 4, 3]
def baseStart_26735 : Nat := 118140960795 + 26735 * 2 ^ 59
def prefixEnd_26735 : Nat := 4983230072969 + 3 ^ 40 * 26735 * 2
def baseEnd_26735 : Nat := 8135054991441856527143

theorem tailTrace_26735 : CollatzResearch.WordTrace tailWord_26735 prefixEnd_26735 8135054991441856527143 := by
  unfold tailWord_26735
  simp only [CollatzResearch.WordTrace]
  refine ⟨975105558151135819593659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 650070372100757213062439 975105558151135819593659)
  ·
    refine ⟨1462658337226703729390489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 975105558151135819593659 1462658337226703729390489)
    ·
      refine ⟨1096993752920027797042867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1462658337226703729390489 1096993752920027797042867)
      ·
        refine ⟨1645490629380041695564301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1096993752920027797042867 1645490629380041695564301)
        ·
          refine ⟨617058986017515635836613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1645490629380041695564301 617058986017515635836613)
          ·
            refine ⟨115698559878284181719365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 617058986017515635836613 115698559878284181719365)
            ·
              refine ⟨21693479977178284072381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115698559878284181719365 21693479977178284072381)
              ·
                refine ⟨8135054991441856527143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21693479977178284072381 8135054991441856527143)
                ·
                  rfl

theorem cell19_26735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 3].length) (baseStart_26735 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_26735 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_26735 prefixEnd_26735 := by exact prefixLift 26735
  have htrace : WordTrace (prefixWord ++ tailWord_26735) baseStart_26735 baseEnd_26735 := by
    simpa [prefixWord, tailWord_26735, baseEnd_26735] using wordTrace_append hprefix tailTrace_26735
  have hstable : (prefixWord ++ tailWord_26735).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26735).length < 2 ^ (prefixWord ++ tailWord_26735).sum := by decide
  have hdescent : baseEnd_26735 < baseStart_26735 := by decide
  rcases family_descends (prefixWord ++ tailWord_26735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26737 : List Nat := [1, 2, 2, 2, 1, 1, 5, 5]
def baseStart_26737 : Nat := 118140960795 + 26737 * 2 ^ 59
def prefixEnd_26737 : Nat := 4983230072969 + 3 ^ 40 * 26737 * 2
def baseEnd_26737 : Nat := 8135663561106444482693

theorem tailTrace_26737 : CollatzResearch.WordTrace tailWord_26737 prefixEnd_26737 8135663561106444482693 := by
  unfold tailWord_26737
  simp only [CollatzResearch.WordTrace]
  refine ⟨975178504143890161166465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 650119002762593440777643 975178504143890161166465)
  ·
    refine ⟨731383878107917620874849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 975178504143890161166465 731383878107917620874849)
    ·
      refine ⟨548537908580938215656137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 731383878107917620874849 548537908580938215656137)
      ·
        refine ⟨411403431435703661742103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 548537908580938215656137 411403431435703661742103)
        ·
          refine ⟨617105147153555492613155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411403431435703661742103 617105147153555492613155)
          ·
            refine ⟨925657720730333238919733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 617105147153555492613155 925657720730333238919733)
            ·
              refine ⟨86780411318468741148725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 925657720730333238919733 86780411318468741148725)
              ·
                refine ⟨8135663561106444482693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86780411318468741148725 8135663561106444482693)
                ·
                  rfl

theorem cell19_26737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 5].length) (baseStart_26737 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_26737 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_26737 prefixEnd_26737 := by exact prefixLift 26737
  have htrace : WordTrace (prefixWord ++ tailWord_26737) baseStart_26737 baseEnd_26737 := by
    simpa [prefixWord, tailWord_26737, baseEnd_26737] using wordTrace_append hprefix tailTrace_26737
  have hstable : (prefixWord ++ tailWord_26737).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26737).length < 2 ^ (prefixWord ++ tailWord_26737).sum := by decide
  have hdescent : baseEnd_26737 < baseStart_26737 := by decide
  rcases family_descends (prefixWord ++ tailWord_26737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26830 : List Nat := [4, 1, 1, 1, 4, 1, 3, 4]
def baseStart_26830 : Nat := 118140960795 + 26830 * 2 ^ 59
def prefixEnd_26830 : Nat := 4983230072969 + 3 ^ 40 * 26830 * 2
def baseEnd_26830 : Nat := 8163962050509784415773

theorem tailTrace_26830 : CollatzResearch.WordTrace tailWord_26830 prefixEnd_26830 8163962050509784415773 := by
  unfold tailWord_26830
  simp only [CollatzResearch.WordTrace]
  refine ⟨122321311600870880537743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 652380328537978029534629 122321311600870880537743)
  ·
    refine ⟨183481967401306320806615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122321311600870880537743 183481967401306320806615)
    ·
      refine ⟨275222951101959481209923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183481967401306320806615 275222951101959481209923)
      ·
        refine ⟨412834426652939221814885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275222951101959481209923 412834426652939221814885)
        ·
          refine ⟨77406454997426104090291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 412834426652939221814885 77406454997426104090291)
          ·
            refine ⟨116109682496139156135437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77406454997426104090291 116109682496139156135437)
            ·
              refine ⟨43541130936052183550789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116109682496139156135437 43541130936052183550789)
              ·
                refine ⟨8163962050509784415773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43541130936052183550789 8163962050509784415773)
                ·
                  rfl

theorem cell19_26830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_26830 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_26830 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_26830 prefixEnd_26830 := by exact prefixLift 26830
  have htrace : WordTrace (prefixWord ++ tailWord_26830) baseStart_26830 baseEnd_26830 := by
    simpa [prefixWord, tailWord_26830, baseEnd_26830] using wordTrace_append hprefix tailTrace_26830
  have hstable : (prefixWord ++ tailWord_26830).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26830).length < 2 ^ (prefixWord ++ tailWord_26830).sum := by decide
  have hdescent : baseEnd_26830 < baseStart_26830 := by decide
  rcases family_descends (prefixWord ++ tailWord_26830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26849 : List Nat := [1, 2, 3, 1, 3, 1, 5, 3]
def baseStart_26849 : Nat := 118140960795 + 26849 * 2 ^ 59
def prefixEnd_26849 : Nat := 4983230072969 + 3 ^ 40 * 26849 * 2
def baseEnd_26849 : Nat := 8169743462323369993499

theorem tailTrace_26849 : CollatzResearch.WordTrace tailWord_26849 prefixEnd_26849 8169743462323369993499 := by
  unfold tailWord_26849
  simp only [CollatzResearch.WordTrace]
  refine ⟨979263479738133289243601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 652842319825422192829067 979263479738133289243601)
  ·
    refine ⟨734447609803599966932701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 979263479738133289243601 734447609803599966932701)
    ·
      refine ⟨275417853676349987599763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 734447609803599966932701 275417853676349987599763)
      ·
        refine ⟨413126780514524981399645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275417853676349987599763 413126780514524981399645)
        ·
          refine ⟨154922542692946868024867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 413126780514524981399645 154922542692946868024867)
          ·
            refine ⟨232383814039420302037301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154922542692946868024867 232383814039420302037301)
            ·
              refine ⟨21785982566195653315997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 232383814039420302037301 21785982566195653315997)
              ·
                refine ⟨8169743462323369993499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21785982566195653315997 8169743462323369993499)
                ·
                  rfl

theorem cell19_26849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 3].length) (baseStart_26849 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_26849 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_26849 prefixEnd_26849 := by exact prefixLift 26849
  have htrace : WordTrace (prefixWord ++ tailWord_26849) baseStart_26849 baseEnd_26849 := by
    simpa [prefixWord, tailWord_26849, baseEnd_26849] using wordTrace_append hprefix tailTrace_26849
  have hstable : (prefixWord ++ tailWord_26849).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26849).length < 2 ^ (prefixWord ++ tailWord_26849).sum := by decide
  have hdescent : baseEnd_26849 < baseStart_26849 := by decide
  rcases family_descends (prefixWord ++ tailWord_26849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26906 : List Nat := [3, 1, 1, 3, 4, 1, 1, 5]
def baseStart_26906 : Nat := 118140960795 + 26906 * 2 ^ 59
def prefixEnd_26906 : Nat := 4983230072969 + 3 ^ 40 * 26906 * 2
def baseEnd_26906 : Nat := 8187087697764126726677

theorem tailTrace_26906 : CollatzResearch.WordTrace tailWord_26906 prefixEnd_26906 8187087697764126726677 := by
  unfold tailWord_26906
  simp only [CollatzResearch.WordTrace]
  refine ⟨245335610132908006017143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 654228293687754682712381 245335610132908006017143)
  ·
    refine ⟨368003415199362009025715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245335610132908006017143 368003415199362009025715)
    ·
      refine ⟨552005122799043013538573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368003415199362009025715 552005122799043013538573)
      ·
        refine ⟨207001921049641130076965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 552005122799043013538573 207001921049641130076965)
        ·
          refine ⟨38812860196807711889431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 207001921049641130076965 38812860196807711889431)
          ·
            refine ⟨58219290295211567834147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38812860196807711889431 58219290295211567834147)
            ·
              refine ⟨87328935442817351751221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58219290295211567834147 87328935442817351751221)
              ·
                refine ⟨8187087697764126726677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87328935442817351751221 8187087697764126726677)
                ·
                  rfl

theorem cell19_26906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 5].length) (baseStart_26906 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_26906 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_26906 prefixEnd_26906 := by exact prefixLift 26906
  have htrace : WordTrace (prefixWord ++ tailWord_26906) baseStart_26906 baseEnd_26906 := by
    simpa [prefixWord, tailWord_26906, baseEnd_26906] using wordTrace_append hprefix tailTrace_26906
  have hstable : (prefixWord ++ tailWord_26906).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26906).length < 2 ^ (prefixWord ++ tailWord_26906).sum := by decide
  have hdescent : baseEnd_26906 < baseStart_26906 := by decide
  rcases family_descends (prefixWord ++ tailWord_26906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26919 : List Nat := [1, 1, 8, 1, 2, 1, 5]
def baseStart_26919 : Nat := 118140960795 + 26919 * 2 ^ 59
def prefixEnd_26919 : Nat := 4983230072969 + 3 ^ 40 * 26919 * 2
def baseEnd_26919 : Nat := 2730347800194649479251

theorem tailTrace_26919 : CollatzResearch.WordTrace tailWord_26919 prefixEnd_26919 2730347800194649479251 := by
  unfold tailWord_26919
  simp only [CollatzResearch.WordTrace]
  refine ⟨981816589484535244291811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 654544392989690162861207 981816589484535244291811)
  ·
    refine ⟨1472724884226802866437717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 981816589484535244291811 1472724884226802866437717)
    ·
      refine ⟨17258494737032846091067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 1472724884226802866437717 17258494737032846091067)
      ·
        refine ⟨25887742105549269136601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17258494737032846091067 25887742105549269136601)
        ·
          refine ⟨19415806579161951852451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25887742105549269136601 19415806579161951852451)
          ·
            refine ⟨29123709868742927778677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19415806579161951852451 29123709868742927778677)
            ·
              refine ⟨2730347800194649479251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29123709868742927778677 2730347800194649479251)
              ·
                rfl

theorem cell19_26919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 5].length) (baseStart_26919 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_26919 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_26919 prefixEnd_26919 := by exact prefixLift 26919
  have htrace : WordTrace (prefixWord ++ tailWord_26919) baseStart_26919 baseEnd_26919 := by
    simpa [prefixWord, tailWord_26919, baseEnd_26919] using wordTrace_append hprefix tailTrace_26919
  have hstable : (prefixWord ++ tailWord_26919).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26919).length < 2 ^ (prefixWord ++ tailWord_26919).sum := by decide
  have hdescent : baseEnd_26919 < baseStart_26919 := by decide
  rcases family_descends (prefixWord ++ tailWord_26919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26984 : List Nat := [2, 1, 4, 2, 2, 8]
def baseStart_26984 : Nat := 118140960795 + 26984 * 2 ^ 59
def prefixEnd_26984 : Nat := 4983230072969 + 3 ^ 40 * 26984 * 2
def baseEnd_26984 : Nat := 912313546075895221459

theorem tailTrace_26984 : CollatzResearch.WordTrace tailWord_26984 prefixEnd_26984 912313546075895221459 := by
  unfold tailWord_26984
  simp only [CollatzResearch.WordTrace]
  refine ⟨492093667124525672704003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 656124889499367563605337 492093667124525672704003)
  ·
    refine ⟨738140500686788509056005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 492093667124525672704003 738140500686788509056005)
    ·
      refine ⟨138401343878772845448001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 738140500686788509056005 138401343878772845448001)
      ·
        refine ⟨103801007909079634086001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138401343878772845448001 103801007909079634086001)
        ·
          refine ⟨77850755931809725564501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103801007909079634086001 77850755931809725564501)
          ·
            refine ⟨912313546075895221459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 77850755931809725564501 912313546075895221459)
            ·
              rfl

theorem cell19_26984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 8].length) (baseStart_26984 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_26984 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_26984 prefixEnd_26984 := by exact prefixLift 26984
  have htrace : WordTrace (prefixWord ++ tailWord_26984) baseStart_26984 baseEnd_26984 := by
    simpa [prefixWord, tailWord_26984, baseEnd_26984] using wordTrace_append hprefix tailTrace_26984
  have hstable : (prefixWord ++ tailWord_26984).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26984).length < 2 ^ (prefixWord ++ tailWord_26984).sum := by decide
  have hdescent : baseEnd_26984 < baseStart_26984 := by decide
  rcases family_descends (prefixWord ++ tailWord_26984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27003 : List Nat := [1, 1, 1, 1, 1, 7, 3, 4]
def baseStart_27003 : Nat := 118140960795 + 27003 * 2 ^ 59
def prefixEnd_27003 : Nat := 4983230072969 + 3 ^ 40 * 27003 * 2
def baseEnd_27003 : Nat := 8216603326496642570857

theorem tailTrace_27003 : CollatzResearch.WordTrace tailWord_27003 prefixEnd_27003 8216603326496642570857 := by
  unfold tailWord_27003
  simp only [CollatzResearch.WordTrace]
  refine ⟨984880321180217590349663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 656586880786811726899775 984880321180217590349663)
  ·
    refine ⟨1477320481770326385524495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 984880321180217590349663 1477320481770326385524495)
    ·
      refine ⟨2215980722655489578286743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1477320481770326385524495 2215980722655489578286743)
      ·
        refine ⟨3323971083983234367430115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2215980722655489578286743 3323971083983234367430115)
        ·
          refine ⟨4985956625974851551145173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3323971083983234367430115 4985956625974851551145173)
          ·
            refine ⟨116858358421285583229965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 4985956625974851551145173 116858358421285583229965)
            ·
              refine ⟨43821884407982093711237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116858358421285583229965 43821884407982093711237)
              ·
                refine ⟨8216603326496642570857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43821884407982093711237 8216603326496642570857)
                ·
                  rfl

theorem cell19_27003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 4].length) (baseStart_27003 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_27003 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_27003 prefixEnd_27003 := by exact prefixLift 27003
  have htrace : WordTrace (prefixWord ++ tailWord_27003) baseStart_27003 baseEnd_27003 := by
    simpa [prefixWord, tailWord_27003, baseEnd_27003] using wordTrace_append hprefix tailTrace_27003
  have hstable : (prefixWord ++ tailWord_27003).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27003).length < 2 ^ (prefixWord ++ tailWord_27003).sum := by decide
  have hdescent : baseEnd_27003 < baseStart_27003 := by decide
  rcases family_descends (prefixWord ++ tailWord_27003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27020 : List Nat := [2, 2, 1, 2, 1, 5, 3, 3]
def baseStart_27020 : Nat := 118140960795 + 27020 * 2 ^ 59
def prefixEnd_27020 : Nat := 4983230072969 + 3 ^ 40 * 27020 * 2
def baseEnd_27020 : Nat := 8221776168645640193033

theorem tailTrace_27020 : CollatzResearch.WordTrace tailWord_27020 prefixEnd_27020 8221776168645640193033 := by
  unfold tailWord_27020
  simp only [CollatzResearch.WordTrace]
  refine ⟨492750181059314746859257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 657000241412419662479009 492750181059314746859257)
  ·
    refine ⟨369562635794486060144443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 492750181059314746859257 369562635794486060144443)
    ·
      refine ⟨554343953691729090216665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369562635794486060144443 554343953691729090216665)
      ·
        refine ⟨415757965268796817662499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 554343953691729090216665 415757965268796817662499)
        ·
          refine ⟨623636947903195226493749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415757965268796817662499 623636947903195226493749)
          ·
            refine ⟨58465963865924552483789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 623636947903195226493749 58465963865924552483789)
            ·
              refine ⟨21924736449721707181421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58465963865924552483789 21924736449721707181421)
              ·
                refine ⟨8221776168645640193033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21924736449721707181421 8221776168645640193033)
                ·
                  rfl

theorem cell19_27020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 3].length) (baseStart_27020 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_27020 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_27020 prefixEnd_27020 := by exact prefixLift 27020
  have htrace : WordTrace (prefixWord ++ tailWord_27020) baseStart_27020 baseEnd_27020 := by
    simpa [prefixWord, tailWord_27020, baseEnd_27020] using wordTrace_append hprefix tailTrace_27020
  have hstable : (prefixWord ++ tailWord_27020).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27020).length < 2 ^ (prefixWord ++ tailWord_27020).sum := by decide
  have hdescent : baseEnd_27020 < baseStart_27020 := by decide
  rcases family_descends (prefixWord ++ tailWord_27020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27073 : List Nat := [1, 2, 7, 1, 1, 1, 1, 5]
def baseStart_27073 : Nat := 118140960795 + 27073 * 2 ^ 59
def prefixEnd_27073 : Nat := 4983230072969 + 3 ^ 40 * 27073 * 2
def baseEnd_27073 : Nat := 8237903264757221015111

theorem tailTrace_27073 : CollatzResearch.WordTrace tailWord_27073 prefixEnd_27073 8237903264757221015111 := by
  unfold tailWord_27073
  simp only [CollatzResearch.WordTrace]
  refine ⟨987433430926619545397873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 658288953951079696931915 987433430926619545397873)
  ·
    refine ⟨740575073194964659048405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 987433430926619545397873 740575073194964659048405)
    ·
      refine ⟨17357228278006984196447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 740575073194964659048405 17357228278006984196447)
      ·
        refine ⟨26035842417010476294671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17357228278006984196447 26035842417010476294671)
        ·
          refine ⟨39053763625515714442007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26035842417010476294671 39053763625515714442007)
          ·
            refine ⟨58580645438273571663011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39053763625515714442007 58580645438273571663011)
            ·
              refine ⟨87870968157410357494517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58580645438273571663011 87870968157410357494517)
              ·
                refine ⟨8237903264757221015111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87870968157410357494517 8237903264757221015111)
                ·
                  rfl

theorem cell19_27073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 5].length) (baseStart_27073 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_27073 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_27073 prefixEnd_27073 := by exact prefixLift 27073
  have htrace : WordTrace (prefixWord ++ tailWord_27073) baseStart_27073 baseEnd_27073 := by
    simpa [prefixWord, tailWord_27073, baseEnd_27073] using wordTrace_append hprefix tailTrace_27073
  have hstable : (prefixWord ++ tailWord_27073).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27073).length < 2 ^ (prefixWord ++ tailWord_27073).sum := by decide
  have hdescent : baseEnd_27073 < baseStart_27073 := by decide
  rcases family_descends (prefixWord ++ tailWord_27073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27079 : List Nat := [1, 1, 4, 1, 1, 5, 1, 5]
def baseStart_27079 : Nat := 118140960795 + 27079 * 2 ^ 59
def prefixEnd_27079 : Nat := 4983230072969 + 3 ^ 40 * 27079 * 2
def baseEnd_27079 : Nat := 8239728973750984881761

theorem tailTrace_27079 : CollatzResearch.WordTrace tailWord_27079 prefixEnd_27079 8239728973750984881761 := by
  unfold tailWord_27079
  simp only [CollatzResearch.WordTrace]
  refine ⟨987652268904882570116291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 658434845936588380077527 987652268904882570116291)
  ·
    refine ⟨1481478403357323855174437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 987652268904882570116291 1481478403357323855174437)
    ·
      refine ⟨277777200629498222845207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1481478403357323855174437 277777200629498222845207)
      ·
        refine ⟨416665800944247334267811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277777200629498222845207 416665800944247334267811)
        ·
          refine ⟨624998701416371001401717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 416665800944247334267811 624998701416371001401717)
          ·
            refine ⟨58593628257784781381411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 624998701416371001401717 58593628257784781381411)
            ·
              refine ⟨87890442386677172072117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58593628257784781381411 87890442386677172072117)
              ·
                refine ⟨8239728973750984881761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87890442386677172072117 8239728973750984881761)
                ·
                  rfl

theorem cell19_27079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 5].length) (baseStart_27079 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_27079 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_27079 prefixEnd_27079 := by exact prefixLift 27079
  have htrace : WordTrace (prefixWord ++ tailWord_27079) baseStart_27079 baseEnd_27079 := by
    simpa [prefixWord, tailWord_27079, baseEnd_27079] using wordTrace_append hprefix tailTrace_27079
  have hstable : (prefixWord ++ tailWord_27079).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27079).length < 2 ^ (prefixWord ++ tailWord_27079).sum := by decide
  have hdescent : baseEnd_27079 < baseStart_27079 := by decide
  rcases family_descends (prefixWord ++ tailWord_27079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27246 : List Nat := [4, 1, 2, 2, 2, 3, 2, 3]
def baseStart_27246 : Nat := 118140960795 + 27246 * 2 ^ 59
def prefixEnd_27246 : Nat := 4983230072969 + 3 ^ 40 * 27246 * 2
def baseEnd_27246 : Nat := 8290544540744079170195

theorem tailTrace_27246 : CollatzResearch.WordTrace tailWord_27246 prefixEnd_27246 8290544540744079170195 := by
  unfold tailWord_27246
  simp only [CollatzResearch.WordTrace]
  refine ⟨124217907412483761430699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 662495506199913394297061 124217907412483761430699)
  ·
    refine ⟨186326861118725642146049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124217907412483761430699 186326861118725642146049)
    ·
      refine ⟨139745145839044231609537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186326861118725642146049 139745145839044231609537)
      ·
        refine ⟨104808859379283173707153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139745145839044231609537 104808859379283173707153)
        ·
          refine ⟨78606644534462380280365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104808859379283173707153 78606644534462380280365)
          ·
            refine ⟨29477491700423392605137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78606644534462380280365 29477491700423392605137)
            ·
              refine ⟨22108118775317544453853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29477491700423392605137 22108118775317544453853)
              ·
                refine ⟨8290544540744079170195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22108118775317544453853 8290544540744079170195)
                ·
                  rfl

theorem cell19_27246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_27246 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_27246 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_27246 prefixEnd_27246 := by exact prefixLift 27246
  have htrace : WordTrace (prefixWord ++ tailWord_27246) baseStart_27246 baseEnd_27246 := by
    simpa [prefixWord, tailWord_27246, baseEnd_27246] using wordTrace_append hprefix tailTrace_27246
  have hstable : (prefixWord ++ tailWord_27246).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27246).length < 2 ^ (prefixWord ++ tailWord_27246).sum := by decide
  have hdescent : baseEnd_27246 < baseStart_27246 := by decide
  rcases family_descends (prefixWord ++ tailWord_27246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27269 : List Nat := [1, 3, 1, 1, 4, 4, 5]
def baseStart_27269 : Nat := 118140960795 + 27269 * 2 ^ 59
def prefixEnd_27269 : Nat := 4983230072969 + 3 ^ 40 * 27269 * 2
def baseEnd_27269 : Nat := 2765847697295613553007

theorem tailTrace_27269 : CollatzResearch.WordTrace tailWord_27269 prefixEnd_27269 2765847697295613553007 := by
  unfold tailWord_27269
  simp only [CollatzResearch.WordTrace]
  refine ⟨994582138216545019532861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 663054758811030013021907 994582138216545019532861)
  ·
    refine ⟨372968301831204382324823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 994582138216545019532861 372968301831204382324823)
    ·
      refine ⟨559452452746806573487235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372968301831204382324823 559452452746806573487235)
      ·
        refine ⟨839178679120209860230853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 559452452746806573487235 839178679120209860230853)
        ·
          refine ⟨157346002335039348793285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 839178679120209860230853 157346002335039348793285)
          ·
            refine ⟨29502375437819877898741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 157346002335039348793285 29502375437819877898741)
            ·
              refine ⟨2765847697295613553007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29502375437819877898741 2765847697295613553007)
              ·
                rfl

theorem cell19_27269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 5].length) (baseStart_27269 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_27269 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_27269 prefixEnd_27269 := by exact prefixLift 27269
  have htrace : WordTrace (prefixWord ++ tailWord_27269) baseStart_27269 baseEnd_27269 := by
    simpa [prefixWord, tailWord_27269, baseEnd_27269] using wordTrace_append hprefix tailTrace_27269
  have hstable : (prefixWord ++ tailWord_27269).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27269).length < 2 ^ (prefixWord ++ tailWord_27269).sum := by decide
  have hdescent : baseEnd_27269 < baseStart_27269 := by decide
  rcases family_descends (prefixWord ++ tailWord_27269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27288 : List Nat := [2, 1, 2, 4, 1, 1, 4, 4]
def baseStart_27288 : Nat := 118140960795 + 27288 * 2 ^ 59
def prefixEnd_27288 : Nat := 4983230072969 + 3 ^ 40 * 27288 * 2
def baseEnd_27288 : Nat := 8303324503700426236747

theorem tailTrace_27288 : CollatzResearch.WordTrace tailWord_27288 prefixEnd_27288 8303324503700426236747 := by
  unfold tailWord_27288
  simp only [CollatzResearch.WordTrace]
  refine ⟨497637562573855632237259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 663516750098474176316345 497637562573855632237259)
  ·
    refine ⟨746456343860783448355889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 497637562573855632237259 746456343860783448355889)
    ·
      refine ⟨559842257895587586266917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 746456343860783448355889 559842257895587586266917)
      ·
        refine ⟨104970423355422672425047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 559842257895587586266917 104970423355422672425047)
        ·
          refine ⟨157455635033134008637571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104970423355422672425047 157455635033134008637571)
          ·
            refine ⟨236183452549701012956357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157455635033134008637571 236183452549701012956357)
            ·
              refine ⟨44284397353068939929317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 236183452549701012956357 44284397353068939929317)
              ·
                refine ⟨8303324503700426236747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44284397353068939929317 8303324503700426236747)
                ·
                  rfl

theorem cell19_27288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 4].length) (baseStart_27288 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_27288 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_27288 prefixEnd_27288 := by exact prefixLift 27288
  have htrace : WordTrace (prefixWord ++ tailWord_27288) baseStart_27288 baseEnd_27288 := by
    simpa [prefixWord, tailWord_27288, baseEnd_27288] using wordTrace_append hprefix tailTrace_27288
  have hstable : (prefixWord ++ tailWord_27288).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27288).length < 2 ^ (prefixWord ++ tailWord_27288).sum := by decide
  have hdescent : baseEnd_27288 < baseStart_27288 := by decide
  rcases family_descends (prefixWord ++ tailWord_27288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27328 : List Nat := [2, 1, 1, 2, 4, 9]
def baseStart_27328 : Nat := 118140960795 + 27328 * 2 ^ 59
def prefixEnd_27328 : Nat := 4983230072969 + 3 ^ 40 * 27328 * 2
def baseEnd_27328 : Nat := 923943988554687260861

theorem tailTrace_27328 : CollatzResearch.WordTrace tailWord_27328 prefixEnd_27328 923943988554687260861 := by
  unfold tailWord_27328
  simp only [CollatzResearch.WordTrace]
  refine ⟨498367022501399047965319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 664489363335198730620425 498367022501399047965319)
  ·
    refine ⟨747550533752098571947979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 498367022501399047965319 747550533752098571947979)
    ·
      refine ⟨1121325800628147857921969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 747550533752098571947979 1121325800628147857921969)
      ·
        refine ⟨840994350471110893441477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1121325800628147857921969 840994350471110893441477)
        ·
          refine ⟨157686440713333292520277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 840994350471110893441477 157686440713333292520277)
          ·
            refine ⟨923943988554687260861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 157686440713333292520277 923943988554687260861)
            ·
              rfl

theorem cell19_27328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 9].length) (baseStart_27328 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_27328 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_27328 prefixEnd_27328 := by exact prefixLift 27328
  have htrace : WordTrace (prefixWord ++ tailWord_27328) baseStart_27328 baseEnd_27328 := by
    simpa [prefixWord, tailWord_27328, baseEnd_27328] using wordTrace_append hprefix tailTrace_27328
  have hstable : (prefixWord ++ tailWord_27328).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27328).length < 2 ^ (prefixWord ++ tailWord_27328).sum := by decide
  have hdescent : baseEnd_27328 < baseStart_27328 := by decide
  rcases family_descends (prefixWord ++ tailWord_27328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27404 : List Nat := [2, 2, 1, 2, 2, 1, 1, 8]
def baseStart_27404 : Nat := 118140960795 + 27404 * 2 ^ 59
def prefixEnd_27404 : Nat := 4983230072969 + 3 ^ 40 * 27404 * 2
def baseEnd_27404 : Nat := 8338621544246527658653

theorem tailTrace_27404 : CollatzResearch.WordTrace tailWord_27404 prefixEnd_27404 8338621544246527658653 := by
  unfold tailWord_27404
  simp only [CollatzResearch.WordTrace]
  refine ⟨499752996363731537848633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 666337328484975383798177 499752996363731537848633)
  ·
    refine ⟨374814747272798653386475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 499752996363731537848633 374814747272798653386475)
    ·
      refine ⟨562222120909197980079713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374814747272798653386475 562222120909197980079713)
      ·
        refine ⟨421666590681898485059785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 562222120909197980079713 421666590681898485059785)
        ·
          refine ⟨316249943011423863794839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 421666590681898485059785 316249943011423863794839)
          ·
            refine ⟨474374914517135795692259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316249943011423863794839 474374914517135795692259)
            ·
              refine ⟨711562371775703693538389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 474374914517135795692259 711562371775703693538389)
              ·
                refine ⟨8338621544246527658653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 711562371775703693538389 8338621544246527658653)
                ·
                  rfl

theorem cell19_27404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 8].length) (baseStart_27404 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_27404 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_27404 prefixEnd_27404 := by exact prefixLift 27404
  have htrace : WordTrace (prefixWord ++ tailWord_27404) baseStart_27404 baseEnd_27404 := by
    simpa [prefixWord, tailWord_27404, baseEnd_27404] using wordTrace_append hprefix tailTrace_27404
  have hstable : (prefixWord ++ tailWord_27404).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27404).length < 2 ^ (prefixWord ++ tailWord_27404).sum := by decide
  have hdescent : baseEnd_27404 < baseStart_27404 := by decide
  rcases family_descends (prefixWord ++ tailWord_27404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27438 : List Nat := [4, 1, 3, 2, 1, 3, 5]
def baseStart_27438 : Nat := 118140960795 + 27438 * 2 ^ 59
def prefixEnd_27438 : Nat := 4983230072969 + 3 ^ 40 * 27438 * 2
def baseEnd_27438 : Nat := 2782989076181507634335

theorem tailTrace_27438 : CollatzResearch.WordTrace tailWord_27438 prefixEnd_27438 2782989076181507634335 := by
  unfold tailWord_27438
  simp only [CollatzResearch.WordTrace]
  refine ⟨125093259325535860304371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 667164049736191254956645 125093259325535860304371)
  ·
    refine ⟨187639888988303790456557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125093259325535860304371 187639888988303790456557)
    ·
      refine ⟨70364958370613921421209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187639888988303790456557 70364958370613921421209)
      ·
        refine ⟨52773718777960441065907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70364958370613921421209 52773718777960441065907)
        ·
          refine ⟨79160578166940661598861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52773718777960441065907 79160578166940661598861)
          ·
            refine ⟨29685216812602748099573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79160578166940661598861 29685216812602748099573)
            ·
              refine ⟨2782989076181507634335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29685216812602748099573 2782989076181507634335)
              ·
                rfl

theorem cell19_27438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 5].length) (baseStart_27438 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_27438 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_27438 prefixEnd_27438 := by exact prefixLift 27438
  have htrace : WordTrace (prefixWord ++ tailWord_27438) baseStart_27438 baseEnd_27438 := by
    simpa [prefixWord, tailWord_27438, baseEnd_27438] using wordTrace_append hprefix tailTrace_27438
  have hstable : (prefixWord ++ tailWord_27438).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27438).length < 2 ^ (prefixWord ++ tailWord_27438).sum := by decide
  have hdescent : baseEnd_27438 < baseStart_27438 := by decide
  rcases family_descends (prefixWord ++ tailWord_27438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27554 : List Nat := [3, 3, 1, 2, 2, 2, 6]
def baseStart_27554 : Nat := 118140960795 + 27554 * 2 ^ 59
def prefixEnd_27554 : Nat := 4983230072969 + 3 ^ 40 * 27554 * 2
def baseEnd_27554 : Nat := 2794754756363541441637

theorem tailTrace_27554 : CollatzResearch.WordTrace tailWord_27554 prefixEnd_27554 2794754756363541441637 := by
  unfold tailWord_27554
  simp only [CollatzResearch.WordTrace]
  refine ⟨251244235546009673414429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 669984628122692462438477 251244235546009673414429)
  ·
    refine ⟨94216588329753627530411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251244235546009673414429 94216588329753627530411)
    ·
      refine ⟨141324882494630441295617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94216588329753627530411 141324882494630441295617)
      ·
        refine ⟨105993661870972830971713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141324882494630441295617 105993661870972830971713)
        ·
          refine ⟨79495246403229623228785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105993661870972830971713 79495246403229623228785)
          ·
            refine ⟨59621434802422217421589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79495246403229623228785 59621434802422217421589)
            ·
              refine ⟨2794754756363541441637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 59621434802422217421589 2794754756363541441637)
              ·
                rfl

theorem cell19_27554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 6].length) (baseStart_27554 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_27554 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_27554 prefixEnd_27554 := by exact prefixLift 27554
  have htrace : WordTrace (prefixWord ++ tailWord_27554) baseStart_27554 baseEnd_27554 := by
    simpa [prefixWord, tailWord_27554, baseEnd_27554] using wordTrace_append hprefix tailTrace_27554
  have hstable : (prefixWord ++ tailWord_27554).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27554).length < 2 ^ (prefixWord ++ tailWord_27554).sum := by decide
  have hdescent : baseEnd_27554 < baseStart_27554 := by decide
  rcases family_descends (prefixWord ++ tailWord_27554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27556 : List Nat := [2, 3, 1, 2, 1, 2, 8]
def baseStart_27556 : Nat := 118140960795 + 27556 * 2 ^ 59
def prefixEnd_27556 : Nat := 4983230072969 + 3 ^ 40 * 27556 * 2
def baseEnd_27556 : Nat := 2794957612918404093487

theorem tailTrace_27556 : CollatzResearch.WordTrace tailWord_27556 prefixEnd_27556 2794957612918404093487 := by
  unfold tailWord_27556
  simp only [CollatzResearch.WordTrace]
  refine ⟨502524944088396517615261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 670033258784528690153681 502524944088396517615261)
  ·
    refine ⟨188446854033148694105723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 502524944088396517615261 188446854033148694105723)
    ·
      refine ⟨282670281049723041158585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188446854033148694105723 282670281049723041158585)
      ·
        refine ⟨212002710787292280868939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282670281049723041158585 212002710787292280868939)
        ·
          refine ⟨318004066180938421303409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212002710787292280868939 318004066180938421303409)
          ·
            refine ⟨238503049635703815977557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 318004066180938421303409 238503049635703815977557)
            ·
              refine ⟨2794957612918404093487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 238503049635703815977557 2794957612918404093487)
              ·
                rfl

theorem cell19_27556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 8].length) (baseStart_27556 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_27556 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_27556 prefixEnd_27556 := by exact prefixLift 27556
  have htrace : WordTrace (prefixWord ++ tailWord_27556) baseStart_27556 baseEnd_27556 := by
    simpa [prefixWord, tailWord_27556, baseEnd_27556] using wordTrace_append hprefix tailTrace_27556
  have hstable : (prefixWord ++ tailWord_27556).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27556).length < 2 ^ (prefixWord ++ tailWord_27556).sum := by decide
  have hdescent : baseEnd_27556 < baseStart_27556 := by decide
  rcases family_descends (prefixWord ++ tailWord_27556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27592 : List Nat := [2, 1, 3, 1, 5, 1, 1, 5]
def baseStart_27592 : Nat := 118140960795 + 27592 * 2 ^ 59
def prefixEnd_27592 : Nat := 4983230072969 + 3 ^ 40 * 27592 * 2
def baseEnd_27592 : Nat := 8395827092717795480363

theorem tailTrace_27592 : CollatzResearch.WordTrace tailWord_27592 prefixEnd_27592 8395827092717795480363 := by
  unfold tailWord_27592
  simp only [CollatzResearch.WordTrace]
  refine ⟨503181458023185591770515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 670908610697580789027353 503181458023185591770515)
  ·
    refine ⟨754772187034778387655773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 503181458023185591770515 754772187034778387655773)
    ·
      refine ⟨283039570138041895370915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 754772187034778387655773 283039570138041895370915)
      ·
        refine ⟨424559355207062843056373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283039570138041895370915 424559355207062843056373)
        ·
          refine ⟨39802439550662141536535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 424559355207062843056373 39802439550662141536535)
          ·
            refine ⟨59703659325993212304803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39802439550662141536535 59703659325993212304803)
            ·
              refine ⟨89555488988989818457205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59703659325993212304803 89555488988989818457205)
              ·
                refine ⟨8395827092717795480363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89555488988989818457205 8395827092717795480363)
                ·
                  rfl

theorem cell19_27592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 5].length) (baseStart_27592 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_27592 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_27592 prefixEnd_27592 := by exact prefixLift 27592
  have htrace : WordTrace (prefixWord ++ tailWord_27592) baseStart_27592 baseEnd_27592 := by
    simpa [prefixWord, tailWord_27592, baseEnd_27592] using wordTrace_append hprefix tailTrace_27592
  have hstable : (prefixWord ++ tailWord_27592).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27592).length < 2 ^ (prefixWord ++ tailWord_27592).sum := by decide
  have hdescent : baseEnd_27592 < baseStart_27592 := by decide
  rcases family_descends (prefixWord ++ tailWord_27592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27666 : List Nat := [3, 2, 5, 1, 8]
def baseStart_27666 : Nat := 118140960795 + 27666 * 2 ^ 59
def prefixEnd_27666 : Nat := 4983230072969 + 3 ^ 40 * 27666 * 2
def baseEnd_27666 : Nat := 311790524826205549471

theorem tailTrace_27666 : CollatzResearch.WordTrace tailWord_27666 prefixEnd_27666 311790524826205549471 := by
  unfold tailWord_27666
  simp only [CollatzResearch.WordTrace]
  refine ⟨252265479444570455433713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 672707945185521214489901 252265479444570455433713)
  ·
    refine ⟨189199109583427841575285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252265479444570455433713 189199109583427841575285)
    ·
      refine ⟨17737416523446360147683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 189199109583427841575285 17737416523446360147683)
      ·
        refine ⟨26606124785169540221525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17737416523446360147683 26606124785169540221525)
        ·
          refine ⟨311790524826205549471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 26606124785169540221525 311790524826205549471)
          ·
            rfl

theorem cell19_27666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 8].length) (baseStart_27666 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_27666 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_27666 prefixEnd_27666 := by exact prefixLift 27666
  have htrace : WordTrace (prefixWord ++ tailWord_27666) baseStart_27666 baseEnd_27666 := by
    simpa [prefixWord, tailWord_27666, baseEnd_27666] using wordTrace_append hprefix tailTrace_27666
  have hstable : (prefixWord ++ tailWord_27666).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27666).length < 2 ^ (prefixWord ++ tailWord_27666).sum := by decide
  have hdescent : baseEnd_27666 < baseStart_27666 := by decide
  rcases family_descends (prefixWord ++ tailWord_27666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27725 : List Nat := [1, 6, 1, 1, 1, 3, 6]
def baseStart_27725 : Nat := 118140960795 + 27725 * 2 ^ 59
def prefixEnd_27725 : Nat := 4983230072969 + 3 ^ 40 * 27725 * 2
def baseEnd_27725 : Nat := 2812098991804298174815

theorem tailTrace_27725 : CollatzResearch.WordTrace tailWord_27725 prefixEnd_27725 2812098991804298174815 := by
  unfold tailWord_27725
  simp only [CollatzResearch.WordTrace]
  refine ⟨1011213824564534898132629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 674142549709689932088419 1011213824564534898132629)
  ·
    refine ⟨47400648026462573349967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1011213824564534898132629 47400648026462573349967)
    ·
      refine ⟨71100972039693860024951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47400648026462573349967 71100972039693860024951)
      ·
        refine ⟨106651458059540790037427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71100972039693860024951 106651458059540790037427)
        ·
          refine ⟨159977187089311185056141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106651458059540790037427 159977187089311185056141)
          ·
            refine ⟨59991445158491694396053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159977187089311185056141 59991445158491694396053)
            ·
              refine ⟨2812098991804298174815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 59991445158491694396053 2812098991804298174815)
              ·
                rfl

theorem cell19_27725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 6].length) (baseStart_27725 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_27725 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_27725 prefixEnd_27725 := by exact prefixLift 27725
  have htrace : WordTrace (prefixWord ++ tailWord_27725) baseStart_27725 baseEnd_27725 := by
    simpa [prefixWord, tailWord_27725, baseEnd_27725] using wordTrace_append hprefix tailTrace_27725
  have hstable : (prefixWord ++ tailWord_27725).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27725).length < 2 ^ (prefixWord ++ tailWord_27725).sum := by decide
  have hdescent : baseEnd_27725 < baseStart_27725 := by decide
  rcases family_descends (prefixWord ++ tailWord_27725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27892 : List Nat := [2, 6, 1, 2, 1, 1, 6]
def baseStart_27892 : Nat := 118140960795 + 27892 * 2 ^ 59
def prefixEnd_27892 : Nat := 4983230072969 + 3 ^ 40 * 27892 * 2
def baseEnd_27892 : Nat := 2829037514135329604293

theorem tailTrace_27892 : CollatzResearch.WordTrace tailWord_27892 prefixEnd_27892 2829037514135329604293 := by
  unfold tailWord_27892
  simp only [CollatzResearch.WordTrace]
  refine ⟨508652407479761209730965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 678203209973014946307953 508652407479761209730965)
  ·
    refine ⟨23843081600613806706139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 508652407479761209730965 23843081600613806706139)
    ·
      refine ⟨35764622400920710059209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23843081600613806706139 35764622400920710059209)
      ·
        refine ⟨26823466800690532544407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35764622400920710059209 26823466800690532544407)
        ·
          refine ⟨40235200201035798816611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26823466800690532544407 40235200201035798816611)
          ·
            refine ⟨60352800301553698224917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40235200201035798816611 60352800301553698224917)
            ·
              refine ⟨2829037514135329604293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 60352800301553698224917 2829037514135329604293)
              ·
                rfl

theorem cell19_27892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 6].length) (baseStart_27892 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_27892 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_27892 prefixEnd_27892 := by exact prefixLift 27892
  have htrace : WordTrace (prefixWord ++ tailWord_27892) baseStart_27892 baseEnd_27892 := by
    simpa [prefixWord, tailWord_27892, baseEnd_27892] using wordTrace_append hprefix tailTrace_27892
  have hstable : (prefixWord ++ tailWord_27892).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27892).length < 2 ^ (prefixWord ++ tailWord_27892).sum := by decide
  have hdescent : baseEnd_27892 < baseStart_27892 := by decide
  rcases family_descends (prefixWord ++ tailWord_27892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27955 : List Nat := [1, 1, 1, 2, 5, 4, 5]
def baseStart_27955 : Nat := 118140960795 + 27955 * 2 ^ 59
def prefixEnd_27955 : Nat := 4983230072969 + 3 ^ 40 * 27955 * 2
def baseEnd_27955 : Nat := 2835427495613503137569

theorem tailTrace_27955 : CollatzResearch.WordTrace tailWord_27955 prefixEnd_27955 2835427495613503137569 := by
  unfold tailWord_27955
  simp only [CollatzResearch.WordTrace]
  refine ⟨1019602613731284179005319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 679735075820856119336879 1019602613731284179005319)
  ·
    refine ⟨1529403920596926268507979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1019602613731284179005319 1529403920596926268507979)
    ·
      refine ⟨2294105880895389402761969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1529403920596926268507979 2294105880895389402761969)
      ·
        refine ⟨1720579410671542052071477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2294105880895389402761969 1720579410671542052071477)
        ·
          refine ⟨161304319750457067381701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1720579410671542052071477 161304319750457067381701)
          ·
            refine ⟨30244559953210700134069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 161304319750457067381701 30244559953210700134069)
            ·
              refine ⟨2835427495613503137569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30244559953210700134069 2835427495613503137569)
              ·
                rfl

theorem cell19_27955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 5].length) (baseStart_27955 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_27955 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_27955 prefixEnd_27955 := by exact prefixLift 27955
  have htrace : WordTrace (prefixWord ++ tailWord_27955) baseStart_27955 baseEnd_27955 := by
    simpa [prefixWord, tailWord_27955, baseEnd_27955] using wordTrace_append hprefix tailTrace_27955
  have hstable : (prefixWord ++ tailWord_27955).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27955).length < 2 ^ (prefixWord ++ tailWord_27955).sum := by decide
  have hdescent : baseEnd_27955 < baseStart_27955 := by decide
  rcases family_descends (prefixWord ++ tailWord_27955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27972 : List Nat := [2, 3, 4, 1, 1, 1, 1, 6]
def baseStart_27972 : Nat := 118140960795 + 27972 * 2 ^ 59
def prefixEnd_27972 : Nat := 4983230072969 + 3 ^ 40 * 27972 * 2
def baseEnd_27972 : Nat := 8511455328989507034883

theorem tailTrace_27972 : CollatzResearch.WordTrace tailWord_27972 prefixEnd_27972 8511455328989507034883 := by
  unfold tailWord_27972
  simp only [CollatzResearch.WordTrace]
  refine ⟨510111327334848041187085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 680148436446464054916113 510111327334848041187085)
  ·
    refine ⟨191291747750568015445157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 510111327334848041187085 191291747750568015445157)
    ·
      refine ⟨35867202703231502895967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191291747750568015445157 35867202703231502895967)
      ·
        refine ⟨53800804054847254343951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35867202703231502895967 53800804054847254343951)
        ·
          refine ⟨80701206082270881515927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53800804054847254343951 80701206082270881515927)
          ·
            refine ⟨121051809123406322273891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80701206082270881515927 121051809123406322273891)
            ·
              refine ⟨181577713685109483410837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121051809123406322273891 181577713685109483410837)
              ·
                refine ⟨8511455328989507034883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 181577713685109483410837 8511455328989507034883)
                ·
                  rfl

theorem cell19_27972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 6].length) (baseStart_27972 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_27972 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_27972 prefixEnd_27972 := by exact prefixLift 27972
  have htrace : WordTrace (prefixWord ++ tailWord_27972) baseStart_27972 baseEnd_27972 := by
    simpa [prefixWord, tailWord_27972, baseEnd_27972] using wordTrace_append hprefix tailTrace_27972
  have hstable : (prefixWord ++ tailWord_27972).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27972).length < 2 ^ (prefixWord ++ tailWord_27972).sum := by decide
  have hdescent : baseEnd_27972 < baseStart_27972 := by decide
  rcases family_descends (prefixWord ++ tailWord_27972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28010 : List Nat := [3, 1, 3, 3, 3, 6]
def baseStart_28010 : Nat := 118140960795 + 28010 * 2 ^ 59
def prefixEnd_28010 : Nat := 4983230072969 + 3 ^ 40 * 28010 * 2
def baseEnd_28010 : Nat := 947002016957408687815

theorem tailTrace_28010 : CollatzResearch.WordTrace tailWord_28010 prefixEnd_28010 947002016957408687815 := by
  unfold tailWord_28010
  simp only [CollatzResearch.WordTrace]
  refine ⟨255402157133007143064371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 681072419021352381504989 255402157133007143064371)
  ·
    refine ⟨383103235699510714596557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255402157133007143064371 383103235699510714596557)
    ·
      refine ⟨143663713387316517973709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 383103235699510714596557 143663713387316517973709)
      ·
        refine ⟨53873892520243694240141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143663713387316517973709 53873892520243694240141)
        ·
          refine ⟨20202709695091385340053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53873892520243694240141 20202709695091385340053)
          ·
            refine ⟨947002016957408687815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20202709695091385340053 947002016957408687815)
            ·
              rfl

theorem cell19_28010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 6].length) (baseStart_28010 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_28010 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_28010 prefixEnd_28010 := by exact prefixLift 28010
  have htrace : WordTrace (prefixWord ++ tailWord_28010) baseStart_28010 baseEnd_28010 := by
    simpa [prefixWord, tailWord_28010, baseEnd_28010] using wordTrace_append hprefix tailTrace_28010
  have hstable : (prefixWord ++ tailWord_28010).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28010).length < 2 ^ (prefixWord ++ tailWord_28010).sum := by decide
  have hdescent : baseEnd_28010 < baseStart_28010 := by decide
  rcases family_descends (prefixWord ++ tailWord_28010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28046 : List Nat := [4, 1, 1, 4, 2, 1, 3, 3]
def baseStart_28046 : Nat := 118140960795 + 28046 * 2 ^ 59
def prefixEnd_28046 : Nat := 4983230072969 + 3 ^ 40 * 28046 * 2
def baseEnd_28046 : Nat := 8533972406579261390237

theorem tailTrace_28046 : CollatzResearch.WordTrace tailWord_28046 prefixEnd_28046 8533972406579261390237 := by
  unfold tailWord_28046
  simp only [CollatzResearch.WordTrace]
  refine ⟨127865207050200840070999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 681947770934404480378661 127865207050200840070999)
  ·
    refine ⟨191797810575301260106499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127865207050200840070999 191797810575301260106499)
    ·
      refine ⟨287696715862951890159749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191797810575301260106499 287696715862951890159749)
      ·
        refine ⟨53943134224303479404953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 287696715862951890159749 53943134224303479404953)
        ·
          refine ⟨40457350668227609553715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53943134224303479404953 40457350668227609553715)
          ·
            refine ⟨60686026002341414330573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40457350668227609553715 60686026002341414330573)
            ·
              refine ⟨22757259750878030373965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60686026002341414330573 22757259750878030373965)
              ·
                refine ⟨8533972406579261390237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22757259750878030373965 8533972406579261390237)
                ·
                  rfl

theorem cell19_28046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_28046 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_28046 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_28046 prefixEnd_28046 := by exact prefixLift 28046
  have htrace : WordTrace (prefixWord ++ tailWord_28046) baseStart_28046 baseEnd_28046 := by
    simpa [prefixWord, tailWord_28046, baseEnd_28046] using wordTrace_append hprefix tailTrace_28046
  have hstable : (prefixWord ++ tailWord_28046).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28046).length < 2 ^ (prefixWord ++ tailWord_28046).sum := by decide
  have hdescent : baseEnd_28046 < baseStart_28046 := by decide
  rcases family_descends (prefixWord ++ tailWord_28046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28107 : List Nat := [1, 1, 1, 1, 3, 3, 6, 3]
def baseStart_28107 : Nat := 118140960795 + 28107 * 2 ^ 59
def prefixEnd_28107 : Nat := 4983230072969 + 3 ^ 40 * 28107 * 2
def baseEnd_28107 : Nat := 8552533781349194034515

theorem tailTrace_28107 : CollatzResearch.WordTrace tailWord_28107 prefixEnd_28107 8552533781349194034515 := by
  unfold tailWord_28107
  simp only [CollatzResearch.WordTrace]
  refine ⟨1025146509180614138538575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 683431006120409425692383 1025146509180614138538575)
  ·
    refine ⟨1537719763770921207807863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1025146509180614138538575 1537719763770921207807863)
    ·
      refine ⟨2306579645656381811711795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1537719763770921207807863 2306579645656381811711795)
      ·
        refine ⟨3459869468484572717567693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2306579645656381811711795 3459869468484572717567693)
        ·
          refine ⟨1297451050681714769087885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3459869468484572717567693 1297451050681714769087885)
          ·
            refine ⟨486544144005643038407957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1297451050681714769087885 486544144005643038407957)
            ·
              refine ⟨22806756750264517425373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 486544144005643038407957 22806756750264517425373)
              ·
                refine ⟨8552533781349194034515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22806756750264517425373 8552533781349194034515)
                ·
                  rfl

theorem cell19_28107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 3].length) (baseStart_28107 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_28107 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_28107 prefixEnd_28107 := by exact prefixLift 28107
  have htrace : WordTrace (prefixWord ++ tailWord_28107) baseStart_28107 baseEnd_28107 := by
    simpa [prefixWord, tailWord_28107, baseEnd_28107] using wordTrace_append hprefix tailTrace_28107
  have hstable : (prefixWord ++ tailWord_28107).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28107).length < 2 ^ (prefixWord ++ tailWord_28107).sum := by decide
  have hdescent : baseEnd_28107 < baseStart_28107 := by decide
  rcases family_descends (prefixWord ++ tailWord_28107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28145 : List Nat := [1, 2, 2, 2, 3, 3, 2, 4]
def baseStart_28145 : Nat := 118140960795 + 28145 * 2 ^ 59
def prefixEnd_28145 : Nat := 4983230072969 + 3 ^ 40 * 28145 * 2
def baseEnd_28145 : Nat := 8564096604976365189967

theorem tailTrace_28145 : CollatzResearch.WordTrace tailWord_28145 prefixEnd_28145 8564096604976365189967 := by
  unfold tailWord_28145
  simp only [CollatzResearch.WordTrace]
  refine ⟨1026532483042946628421889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 684354988695297752281259 1026532483042946628421889)
  ·
    refine ⟨769899362282209971316417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1026532483042946628421889 769899362282209971316417)
    ·
      refine ⟨577424521711657478487313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 769899362282209971316417 577424521711657478487313)
      ·
        refine ⟨433068391283743108865485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 577424521711657478487313 433068391283743108865485)
        ·
          refine ⟨162400646731403665824557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 433068391283743108865485 162400646731403665824557)
          ·
            refine ⟨60900242524276374684209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162400646731403665824557 60900242524276374684209)
            ·
              refine ⟨45675181893207281013157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60900242524276374684209 45675181893207281013157)
              ·
                refine ⟨8564096604976365189967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45675181893207281013157 8564096604976365189967)
                ·
                  rfl

theorem cell19_28145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 4].length) (baseStart_28145 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_28145 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_28145 prefixEnd_28145 := by exact prefixLift 28145
  have htrace : WordTrace (prefixWord ++ tailWord_28145) baseStart_28145 baseEnd_28145 := by
    simpa [prefixWord, tailWord_28145, baseEnd_28145] using wordTrace_append hprefix tailTrace_28145
  have hstable : (prefixWord ++ tailWord_28145).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28145).length < 2 ^ (prefixWord ++ tailWord_28145).sum := by decide
  have hdescent : baseEnd_28145 < baseStart_28145 := by decide
  rcases family_descends (prefixWord ++ tailWord_28145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28162 : List Nat := [3, 4, 1, 2, 1, 1, 2, 5]
def baseStart_28162 : Nat := 118140960795 + 28162 * 2 ^ 59
def prefixEnd_28162 : Nat := 4983230072969 + 3 ^ 40 * 28162 * 2
def baseEnd_28162 : Nat := 8569269447125362812143

theorem tailTrace_28162 : CollatzResearch.WordTrace tailWord_28162 prefixEnd_28162 8569269447125362812143 := by
  unfold tailWord_28162
  simp only [CollatzResearch.WordTrace]
  refine ⟨256788130995339632947685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 684768349320905687860493 256788130995339632947685)
  ·
    refine ⟨48147774561626181177691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 256788130995339632947685 48147774561626181177691)
    ·
      refine ⟨72221661842439271766537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48147774561626181177691 72221661842439271766537)
      ·
        refine ⟨54166246381829453824903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72221661842439271766537 54166246381829453824903)
        ·
          refine ⟨81249369572744180737355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54166246381829453824903 81249369572744180737355)
          ·
            refine ⟨121874054359116271106033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81249369572744180737355 121874054359116271106033)
            ·
              refine ⟨91405540769337203329525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121874054359116271106033 91405540769337203329525)
              ·
                refine ⟨8569269447125362812143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91405540769337203329525 8569269447125362812143)
                ·
                  rfl

theorem cell19_28162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_28162 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_28162 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_28162 prefixEnd_28162 := by exact prefixLift 28162
  have htrace : WordTrace (prefixWord ++ tailWord_28162) baseStart_28162 baseEnd_28162 := by
    simpa [prefixWord, tailWord_28162, baseEnd_28162] using wordTrace_append hprefix tailTrace_28162
  have hstable : (prefixWord ++ tailWord_28162).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28162).length < 2 ^ (prefixWord ++ tailWord_28162).sum := by decide
  have hdescent : baseEnd_28162 < baseStart_28162 := by decide
  rcases family_descends (prefixWord ++ tailWord_28162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28394 : List Nat := [3, 1, 3, 1, 1, 1, 2, 7]
def baseStart_28394 : Nat := 118140960795 + 28394 * 2 ^ 59
def prefixEnd_28394 : Nat := 4983230072969 + 3 ^ 40 * 28394 * 2
def baseEnd_28394 : Nat := 8639863528217565655955

theorem tailTrace_28394 : CollatzResearch.WordTrace tailWord_28394 prefixEnd_28394 8639863528217565655955 := by
  unfold tailWord_28394
  simp only [CollatzResearch.WordTrace]
  refine ⟨258903564785215538559059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 690409506093908102824157 258903564785215538559059)
  ·
    refine ⟨388355347177823307838589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258903564785215538559059 388355347177823307838589)
    ·
      refine ⟨145633255191683740439471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 388355347177823307838589 145633255191683740439471)
      ·
        refine ⟨218449882787525610659207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145633255191683740439471 218449882787525610659207)
        ·
          refine ⟨327674824181288415988811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218449882787525610659207 327674824181288415988811)
          ·
            refine ⟨491512236271932623983217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327674824181288415988811 491512236271932623983217)
            ·
              refine ⟨368634177203949467987413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 491512236271932623983217 368634177203949467987413)
              ·
                refine ⟨8639863528217565655955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 368634177203949467987413 8639863528217565655955)
                ·
                  rfl

theorem cell19_28394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_28394 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_28394 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_28394 prefixEnd_28394 := by exact prefixLift 28394
  have htrace : WordTrace (prefixWord ++ tailWord_28394) baseStart_28394 baseEnd_28394 := by
    simpa [prefixWord, tailWord_28394, baseEnd_28394] using wordTrace_append hprefix tailTrace_28394
  have hstable : (prefixWord ++ tailWord_28394).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28394).length < 2 ^ (prefixWord ++ tailWord_28394).sum := by decide
  have hdescent : baseEnd_28394 < baseStart_28394 := by decide
  rcases family_descends (prefixWord ++ tailWord_28394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28449 : List Nat := [1, 2, 3, 2, 1, 3, 4, 3]
def baseStart_28449 : Nat := 118140960795 + 28449 * 2 ^ 59
def prefixEnd_28449 : Nat := 4983230072969 + 3 ^ 40 * 28449 * 2
def baseEnd_28449 : Nat := 8656599193993734433583

theorem tailTrace_28449 : CollatzResearch.WordTrace tailWord_28449 prefixEnd_28449 8656599193993734433583 := by
  unfold tailWord_28449
  simp only [CollatzResearch.WordTrace]
  refine ⟨1037620273941606547488401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 691746849294404364992267 1037620273941606547488401)
  ·
    refine ⟨778215205456204910616301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1037620273941606547488401 778215205456204910616301)
    ·
      refine ⟨291830702046076841481113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 778215205456204910616301 291830702046076841481113)
      ·
        refine ⟨218873026534557631110835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291830702046076841481113 218873026534557631110835)
        ·
          refine ⟨328309539801836446666253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218873026534557631110835 328309539801836446666253)
          ·
            refine ⟨123116077425688667499845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 328309539801836446666253 123116077425688667499845)
            ·
              refine ⟨23084264517316625156221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123116077425688667499845 23084264517316625156221)
              ·
                refine ⟨8656599193993734433583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23084264517316625156221 8656599193993734433583)
                ·
                  rfl

theorem cell19_28449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 3].length) (baseStart_28449 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_28449 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_28449 prefixEnd_28449 := by exact prefixLift 28449
  have htrace : WordTrace (prefixWord ++ tailWord_28449) baseStart_28449 baseEnd_28449 := by
    simpa [prefixWord, tailWord_28449, baseEnd_28449] using wordTrace_append hprefix tailTrace_28449
  have hstable : (prefixWord ++ tailWord_28449).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28449).length < 2 ^ (prefixWord ++ tailWord_28449).sum := by decide
  have hdescent : baseEnd_28449 < baseStart_28449 := by decide
  rcases family_descends (prefixWord ++ tailWord_28449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28468 : List Nat := [2, 5, 1, 1, 2, 1, 7]
def baseStart_28468 : Nat := 118140960795 + 28468 * 2 ^ 59
def prefixEnd_28468 : Nat := 4983230072969 + 3 ^ 40 * 28468 * 2
def baseEnd_28468 : Nat := 2887460201935773337103

theorem tailTrace_28468 : CollatzResearch.WordTrace tailWord_28468 prefixEnd_28468 2887460201935773337103 := by
  unfold tailWord_28468
  simp only [CollatzResearch.WordTrace]
  refine ⟨519156630436386396215029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 692208840581848528286705 519156630436386396215029)
  ·
    refine ⟨48670934103411224645159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 519156630436386396215029 48670934103411224645159)
    ·
      refine ⟨73006401155116836967739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48670934103411224645159 73006401155116836967739)
      ·
        refine ⟨109509601732675255451609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73006401155116836967739 109509601732675255451609)
        ·
          refine ⟨82132201299506441588707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109509601732675255451609 82132201299506441588707)
          ·
            refine ⟨123198301949259662383061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82132201299506441588707 123198301949259662383061)
            ·
              refine ⟨2887460201935773337103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 123198301949259662383061 2887460201935773337103)
              ·
                rfl

theorem cell19_28468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 7].length) (baseStart_28468 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_28468 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_28468 prefixEnd_28468 := by exact prefixLift 28468
  have htrace : WordTrace (prefixWord ++ tailWord_28468) baseStart_28468 baseEnd_28468 := by
    simpa [prefixWord, tailWord_28468, baseEnd_28468] using wordTrace_append hprefix tailTrace_28468
  have hstable : (prefixWord ++ tailWord_28468).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28468).length < 2 ^ (prefixWord ++ tailWord_28468).sum := by decide
  have hdescent : baseEnd_28468 < baseStart_28468 := by decide
  rcases family_descends (prefixWord ++ tailWord_28468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28489 : List Nat := [1, 2, 1, 1, 2, 4, 4, 4]
def baseStart_28489 : Nat := 118140960795 + 28489 * 2 ^ 59
def prefixEnd_28489 : Nat := 4983230072969 + 3 ^ 40 * 28489 * 2
def baseEnd_28489 : Nat := 8668770587285493544585

theorem tailTrace_28489 : CollatzResearch.WordTrace tailWord_28489 prefixEnd_28489 8668770587285493544585 := by
  unfold tailWord_28489
  simp only [CollatzResearch.WordTrace]
  refine ⟨1039079193796693378944521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 692719462531128919296347 1039079193796693378944521)
  ·
    refine ⟨779309395347520034208391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1039079193796693378944521 779309395347520034208391)
    ·
      refine ⟨1168964093021280051312587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 779309395347520034208391 1168964093021280051312587)
      ·
        refine ⟨1753446139531920076968881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1168964093021280051312587 1753446139531920076968881)
        ·
          refine ⟨1315084604648940057726661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1753446139531920076968881 1315084604648940057726661)
          ·
            refine ⟨246578363371676260823749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1315084604648940057726661 246578363371676260823749)
            ·
              refine ⟨46233443132189298904453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 246578363371676260823749 46233443132189298904453)
              ·
                refine ⟨8668770587285493544585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46233443132189298904453 8668770587285493544585)
                ·
                  rfl

theorem cell19_28489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 4].length) (baseStart_28489 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_28489 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_28489 prefixEnd_28489 := by exact prefixLift 28489
  have htrace : WordTrace (prefixWord ++ tailWord_28489) baseStart_28489 baseEnd_28489 := by
    simpa [prefixWord, tailWord_28489, baseEnd_28489] using wordTrace_append hprefix tailTrace_28489
  have hstable : (prefixWord ++ tailWord_28489).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28489).length < 2 ^ (prefixWord ++ tailWord_28489).sum := by decide
  have hdescent : baseEnd_28489 < baseStart_28489 := by decide
  rcases family_descends (prefixWord ++ tailWord_28489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28542 : List Nat := [4, 2, 3, 1, 1, 1, 3, 4]
def baseStart_28542 : Nat := 118140960795 + 28542 * 2 ^ 59
def prefixEnd_28542 : Nat := 4983230072969 + 3 ^ 40 * 28542 * 2
def baseEnd_28542 : Nat := 8684897683397074366663

theorem tailTrace_28542 : CollatzResearch.WordTrace tailWord_28542 prefixEnd_28542 8684897683397074366663 := by
  unfold tailWord_28542
  simp only [CollatzResearch.WordTrace]
  refine ⟨130126532825585428827985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 694008175069788953749253 130126532825585428827985)
  ·
    refine ⟨97594899619189071620989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130126532825585428827985 97594899619189071620989)
    ·
      refine ⟨36598087357195901857871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97594899619189071620989 36598087357195901857871)
      ·
        refine ⟨54897131035793852786807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36598087357195901857871 54897131035793852786807)
        ·
          refine ⟨82345696553690779180211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54897131035793852786807 82345696553690779180211)
          ·
            refine ⟨123518544830536168770317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82345696553690779180211 123518544830536168770317)
            ·
              refine ⟨46319454311451063288869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123518544830536168770317 46319454311451063288869)
              ·
                refine ⟨8684897683397074366663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46319454311451063288869 8684897683397074366663)
                ·
                  rfl

theorem cell19_28542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_28542 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_28542 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_28542 prefixEnd_28542 := by exact prefixLift 28542
  have htrace : WordTrace (prefixWord ++ tailWord_28542) baseStart_28542 baseEnd_28542 := by
    simpa [prefixWord, tailWord_28542, baseEnd_28542] using wordTrace_append hprefix tailTrace_28542
  have hstable : (prefixWord ++ tailWord_28542).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28542).length < 2 ^ (prefixWord ++ tailWord_28542).sum := by decide
  have hdescent : baseEnd_28542 < baseStart_28542 := by decide
  rcases family_descends (prefixWord ++ tailWord_28542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28620 : List Nat := [2, 2, 1, 4, 1, 2, 4, 3]
def baseStart_28620 : Nat := 118140960795 + 28620 * 2 ^ 59
def prefixEnd_28620 : Nat := 4983230072969 + 3 ^ 40 * 28620 * 2
def baseEnd_28620 : Nat := 8708631900316004633117

theorem tailTrace_28620 : CollatzResearch.WordTrace tailWord_28620 prefixEnd_28620 8708631900316004633117 := by
  unfold tailWord_28620
  simp only [CollatzResearch.WordTrace]
  refine ⟨521928578161051375981657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 695904770881401834642209 521928578161051375981657)
  ·
    refine ⟨391446433620788531986243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 521928578161051375981657 391446433620788531986243)
    ·
      refine ⟨587169650431182797979365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391446433620788531986243 587169650431182797979365)
      ·
        refine ⟨110094309455846774621131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 587169650431182797979365 110094309455846774621131)
        ·
          refine ⟨165141464183770161931697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110094309455846774621131 165141464183770161931697)
          ·
            refine ⟨123856098137827621448773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165141464183770161931697 123856098137827621448773)
            ·
              refine ⟨23223018400842679021645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123856098137827621448773 23223018400842679021645)
              ·
                refine ⟨8708631900316004633117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23223018400842679021645 8708631900316004633117)
                ·
                  rfl

theorem cell19_28620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 3].length) (baseStart_28620 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_28620 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_28620 prefixEnd_28620 := by exact prefixLift 28620
  have htrace : WordTrace (prefixWord ++ tailWord_28620) baseStart_28620 baseEnd_28620 := by
    simpa [prefixWord, tailWord_28620, baseEnd_28620] using wordTrace_append hprefix tailTrace_28620
  have hstable : (prefixWord ++ tailWord_28620).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28620).length < 2 ^ (prefixWord ++ tailWord_28620).sum := by decide
  have hdescent : baseEnd_28620 < baseStart_28620 := by decide
  rcases family_descends (prefixWord ++ tailWord_28620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28622 : List Nat := [4, 1, 1, 1, 2, 2, 3, 5]
def baseStart_28622 : Nat := 118140960795 + 28622 * 2 ^ 59
def prefixEnd_28622 : Nat := 4983230072969 + 3 ^ 40 * 28622 * 2
def baseEnd_28622 : Nat := 8709240469980592588667

theorem tailTrace_28622 : CollatzResearch.WordTrace tailWord_28622 prefixEnd_28622 8709240469980592588667 := by
  unfold tailWord_28622
  simp only [CollatzResearch.WordTrace]
  refine ⟨130491262789357136692015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 695953401543238062357413 130491262789357136692015)
  ·
    refine ⟨195736894184035705038023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130491262789357136692015 195736894184035705038023)
    ·
      refine ⟨293605341276053557557035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195736894184035705038023 293605341276053557557035)
      ·
        refine ⟨440408011914080336335553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293605341276053557557035 440408011914080336335553)
        ·
          refine ⟨330306008935560252251665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 440408011914080336335553 330306008935560252251665)
          ·
            refine ⟨247729506701670189188749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 330306008935560252251665 247729506701670189188749)
            ·
              refine ⟨92898565013126320945781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 247729506701670189188749 92898565013126320945781)
              ·
                refine ⟨8709240469980592588667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92898565013126320945781 8709240469980592588667)
                ·
                  rfl

theorem cell19_28622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_28622 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_28622 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_28622 prefixEnd_28622 := by exact prefixLift 28622
  have htrace : WordTrace (prefixWord ++ tailWord_28622) baseStart_28622 baseEnd_28622 := by
    simpa [prefixWord, tailWord_28622, baseEnd_28622] using wordTrace_append hprefix tailTrace_28622
  have hstable : (prefixWord ++ tailWord_28622).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28622).length < 2 ^ (prefixWord ++ tailWord_28622).sum := by decide
  have hdescent : baseEnd_28622 < baseStart_28622 := by decide
  rcases family_descends (prefixWord ++ tailWord_28622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28637 : List Nat := [1, 4, 3, 1, 4, 1, 5]
def baseStart_28637 : Nat := 118140960795 + 28637 * 2 ^ 59
def prefixEnd_28637 : Nat := 4983230072969 + 3 ^ 40 * 28637 * 2
def baseEnd_28637 : Nat := 2904601580821667418431

theorem tailTrace_28637 : CollatzResearch.WordTrace tailWord_28637 prefixEnd_28637 2904601580821667418431 := by
  unfold tailWord_28637
  simp only [CollatzResearch.WordTrace]
  refine ⟨1044477197260514655332165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 696318131507009770221443 1044477197260514655332165)
  ·
    refine ⟨195839474486346497874781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1044477197260514655332165 195839474486346497874781)
    ·
      refine ⟨73439802932379936703043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195839474486346497874781 73439802932379936703043)
      ·
        refine ⟨110159704398569905054565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73439802932379936703043 110159704398569905054565)
        ·
          refine ⟨20654944574731857197731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110159704398569905054565 20654944574731857197731)
          ·
            refine ⟨30982416862097785796597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20654944574731857197731 30982416862097785796597)
            ·
              refine ⟨2904601580821667418431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30982416862097785796597 2904601580821667418431)
              ·
                rfl

theorem cell19_28637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 5].length) (baseStart_28637 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_28637 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_28637 prefixEnd_28637 := by exact prefixLift 28637
  have htrace : WordTrace (prefixWord ++ tailWord_28637) baseStart_28637 baseEnd_28637 := by
    simpa [prefixWord, tailWord_28637, baseEnd_28637] using wordTrace_append hprefix tailTrace_28637
  have hstable : (prefixWord ++ tailWord_28637).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28637).length < 2 ^ (prefixWord ++ tailWord_28637).sum := by decide
  have hdescent : baseEnd_28637 < baseStart_28637 := by decide
  rcases family_descends (prefixWord ++ tailWord_28637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28679 : List Nat := [1, 1, 4, 3, 1, 2, 2, 5]
def baseStart_28679 : Nat := 118140960795 + 28679 * 2 ^ 59
def prefixEnd_28679 : Nat := 4983230072969 + 3 ^ 40 * 28679 * 2
def baseEnd_28679 : Nat := 8726584705421349321845

theorem tailTrace_28679 : CollatzResearch.WordTrace tailWord_28679 prefixEnd_28679 8726584705421349321845 := by
  unfold tailWord_28679
  simp only [CollatzResearch.WordTrace]
  refine ⟨1046009063108355828361091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 697339375405570552240727 1046009063108355828361091)
  ·
    refine ⟨1569013594662533742541637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1046009063108355828361091 1569013594662533742541637)
    ·
      refine ⟨294190048999225076726557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1569013594662533742541637 294190048999225076726557)
      ·
        refine ⟨110321268374709403772459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 294190048999225076726557 110321268374709403772459)
        ·
          refine ⟨165481902562064105658689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110321268374709403772459 165481902562064105658689)
          ·
            refine ⟨124111426921548079244017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165481902562064105658689 124111426921548079244017)
            ·
              refine ⟨93083570191161059433013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124111426921548079244017 93083570191161059433013)
              ·
                refine ⟨8726584705421349321845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93083570191161059433013 8726584705421349321845)
                ·
                  rfl

theorem cell19_28679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 5].length) (baseStart_28679 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_28679 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_28679 prefixEnd_28679 := by exact prefixLift 28679
  have htrace : WordTrace (prefixWord ++ tailWord_28679) baseStart_28679 baseEnd_28679 := by
    simpa [prefixWord, tailWord_28679, baseEnd_28679] using wordTrace_append hprefix tailTrace_28679
  have hstable : (prefixWord ++ tailWord_28679).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28679).length < 2 ^ (prefixWord ++ tailWord_28679).sum := by decide
  have hdescent : baseEnd_28679 < baseStart_28679 := by decide
  rcases family_descends (prefixWord ++ tailWord_28679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28711 : List Nat := [1, 1, 7, 1, 3, 1, 1, 4]
def baseStart_28711 : Nat := 118140960795 + 28711 * 2 ^ 59
def prefixEnd_28711 : Nat := 4983230072969 + 3 ^ 40 * 28711 * 2
def baseEnd_28711 : Nat := 8736321820054756610647

theorem tailTrace_28711 : CollatzResearch.WordTrace tailWord_28711 prefixEnd_28711 8736321820054756610647 := by
  unfold tailWord_28711
  simp only [CollatzResearch.WordTrace]
  refine ⟨1047176198992425293525987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 698117465994950195683991 1047176198992425293525987)
  ·
    refine ⟨1570764298488637940288981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1047176198992425293525987 1570764298488637940288981)
    ·
      refine ⟨36814788245827451725523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 1570764298488637940288981 36814788245827451725523)
      ·
        refine ⟨55222182368741177588285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36814788245827451725523 55222182368741177588285)
        ·
          refine ⟨20708318388277941595607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55222182368741177588285 20708318388277941595607)
          ·
            refine ⟨31062477582416912393411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20708318388277941595607 31062477582416912393411)
            ·
              refine ⟨46593716373625368590117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31062477582416912393411 46593716373625368590117)
              ·
                refine ⟨8736321820054756610647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46593716373625368590117 8736321820054756610647)
                ·
                  rfl

theorem cell19_28711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 4].length) (baseStart_28711 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_28711 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_28711 prefixEnd_28711 := by exact prefixLift 28711
  have htrace : WordTrace (prefixWord ++ tailWord_28711) baseStart_28711 baseEnd_28711 := by
    simpa [prefixWord, tailWord_28711, baseEnd_28711] using wordTrace_append hprefix tailTrace_28711
  have hstable : (prefixWord ++ tailWord_28711).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28711).length < 2 ^ (prefixWord ++ tailWord_28711).sum := by decide
  have hdescent : baseEnd_28711 < baseStart_28711 := by decide
  rcases family_descends (prefixWord ++ tailWord_28711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28719 : List Nat := [1, 1, 2, 1, 2, 1, 1, 10]
def baseStart_28719 : Nat := 118140960795 + 28719 * 2 ^ 59
def prefixEnd_28719 : Nat := 4983230072969 + 3 ^ 40 * 28719 * 2
def baseEnd_28719 : Nat := 8738756098713108432847

theorem tailTrace_28719 : CollatzResearch.WordTrace tailWord_28719 prefixEnd_28719 8738756098713108432847 := by
  unfold tailWord_28719
  simp only [CollatzResearch.WordTrace]
  refine ⟨1047467982963442659817211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 698311988642295106544807 1047467982963442659817211)
  ·
    refine ⟨1571201974445163989725817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1047467982963442659817211 1571201974445163989725817)
    ·
      refine ⟨1178401480833872992294363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1571201974445163989725817 1178401480833872992294363)
      ·
        refine ⟨1767602221250809488441545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1178401480833872992294363 1767602221250809488441545)
        ·
          refine ⟨1325701665938107116331159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1767602221250809488441545 1325701665938107116331159)
          ·
            refine ⟨1988552498907160674496739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1325701665938107116331159 1988552498907160674496739)
            ·
              refine ⟨2982828748360741011745109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1988552498907160674496739 2982828748360741011745109)
              ·
                refine ⟨8738756098713108432847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 2982828748360741011745109 8738756098713108432847)
                ·
                  rfl

theorem cell19_28719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 10].length) (baseStart_28719 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_28719 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_28719 prefixEnd_28719 := by exact prefixLift 28719
  have htrace : WordTrace (prefixWord ++ tailWord_28719) baseStart_28719 baseEnd_28719 := by
    simpa [prefixWord, tailWord_28719, baseEnd_28719] using wordTrace_append hprefix tailTrace_28719
  have hstable : (prefixWord ++ tailWord_28719).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28719).length < 2 ^ (prefixWord ++ tailWord_28719).sum := by decide
  have hdescent : baseEnd_28719 < baseStart_28719 := by decide
  rcases family_descends (prefixWord ++ tailWord_28719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28791 : List Nat := [1, 1, 3, 1, 1, 7, 2, 3]
def baseStart_28791 : Nat := 118140960795 + 28791 * 2 ^ 59
def prefixEnd_28791 : Nat := 4983230072969 + 3 ^ 40 * 28791 * 2
def baseEnd_28791 : Nat := 8760664606638274832651

theorem tailTrace_28791 : CollatzResearch.WordTrace tailWord_28791 prefixEnd_28791 8760664606638274832651 := by
  unfold tailWord_28791
  simp only [CollatzResearch.WordTrace]
  refine ⟨1050094038702598956438227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 700062692468399304292151 1050094038702598956438227)
  ·
    refine ⟨1575141058053898434657341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1050094038702598956438227 1575141058053898434657341)
    ·
      refine ⟨590677896770211912996503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1575141058053898434657341 590677896770211912996503)
      ·
        refine ⟨886016845155317869494755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 590677896770211912996503 886016845155317869494755)
        ·
          refine ⟨1329025267732976804242133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 886016845155317869494755 1329025267732976804242133)
          ·
            refine ⟨31149029712491643849425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1329025267732976804242133 31149029712491643849425)
            ·
              refine ⟨23361772284368732887069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31149029712491643849425 23361772284368732887069)
              ·
                refine ⟨8760664606638274832651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23361772284368732887069 8760664606638274832651)
                ·
                  rfl

theorem cell19_28791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 3].length) (baseStart_28791 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_28791 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_28791 prefixEnd_28791 := by exact prefixLift 28791
  have htrace : WordTrace (prefixWord ++ tailWord_28791) baseStart_28791 baseEnd_28791 := by
    simpa [prefixWord, tailWord_28791, baseEnd_28791] using wordTrace_append hprefix tailTrace_28791
  have hstable : (prefixWord ++ tailWord_28791).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28791).length < 2 ^ (prefixWord ++ tailWord_28791).sum := by decide
  have hdescent : baseEnd_28791 < baseStart_28791 := by decide
  rcases family_descends (prefixWord ++ tailWord_28791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28793 : List Nat := [1, 2, 1, 3, 4, 2, 1, 5]
def baseStart_28793 : Nat := 118140960795 + 28793 * 2 ^ 59
def prefixEnd_28793 : Nat := 4983230072969 + 3 ^ 40 * 28793 * 2
def baseEnd_28793 : Nat := 8761273176302862788201

theorem tailTrace_28793 : CollatzResearch.WordTrace tailWord_28793 prefixEnd_28793 8761273176302862788201 := by
  unfold tailWord_28793
  simp only [CollatzResearch.WordTrace]
  refine ⟨1050166984695353298011033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 700111323130235532007355 1050166984695353298011033)
  ·
    refine ⟨787625238521514973508275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1050166984695353298011033 787625238521514973508275)
    ·
      refine ⟨1181437857782272460262413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 787625238521514973508275 1181437857782272460262413)
      ·
        refine ⟨443039196668352172598405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1181437857782272460262413 443039196668352172598405)
        ·
          refine ⟨83069849375316032362201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 443039196668352172598405 83069849375316032362201)
          ·
            refine ⟨62302387031487024271651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83069849375316032362201 62302387031487024271651)
            ·
              refine ⟨93453580547230536407477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62302387031487024271651 93453580547230536407477)
              ·
                refine ⟨8761273176302862788201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93453580547230536407477 8761273176302862788201)
                ·
                  rfl

theorem cell19_28793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 5].length) (baseStart_28793 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_28793 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_28793 prefixEnd_28793 := by exact prefixLift 28793
  have htrace : WordTrace (prefixWord ++ tailWord_28793) baseStart_28793 baseEnd_28793 := by
    simpa [prefixWord, tailWord_28793, baseEnd_28793] using wordTrace_append hprefix tailTrace_28793
  have hstable : (prefixWord ++ tailWord_28793).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28793).length < 2 ^ (prefixWord ++ tailWord_28793).sum := by decide
  have hdescent : baseEnd_28793 < baseStart_28793 := by decide
  rcases family_descends (prefixWord ++ tailWord_28793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28831 : List Nat := [1, 1, 2, 6, 1, 1, 1, 6]
def baseStart_28831 : Nat := 118140960795 + 28831 * 2 ^ 59
def prefixEnd_28831 : Nat := 4983230072969 + 3 ^ 40 * 28831 * 2
def baseEnd_28831 : Nat := 8772835999930033943653

theorem tailTrace_28831 : CollatzResearch.WordTrace tailWord_28831 prefixEnd_28831 8772835999930033943653 := by
  unfold tailWord_28831
  simp only [CollatzResearch.WordTrace]
  refine ⟨1051552958557685787894347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 701035305705123858596231 1051552958557685787894347)
  ·
    refine ⟨1577329437836528681841521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1051552958557685787894347 1577329437836528681841521)
    ·
      refine ⟨1182997078377396511381141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1577329437836528681841521 1182997078377396511381141)
      ·
        refine ⟨55452988048940461470991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1182997078377396511381141 55452988048940461470991)
        ·
          refine ⟨83179482073410692206487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55452988048940461470991 83179482073410692206487)
          ·
            refine ⟨124769223110116038309731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83179482073410692206487 124769223110116038309731)
            ·
              refine ⟨187153834665174057464597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124769223110116038309731 187153834665174057464597)
              ·
                refine ⟨8772835999930033943653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 187153834665174057464597 8772835999930033943653)
                ·
                  rfl

theorem cell19_28831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 6].length) (baseStart_28831 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_28831 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_28831 prefixEnd_28831 := by exact prefixLift 28831
  have htrace : WordTrace (prefixWord ++ tailWord_28831) baseStart_28831 baseEnd_28831 := by
    simpa [prefixWord, tailWord_28831, baseEnd_28831] using wordTrace_append hprefix tailTrace_28831
  have hstable : (prefixWord ++ tailWord_28831).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28831).length < 2 ^ (prefixWord ++ tailWord_28831).sum := by decide
  have hdescent : baseEnd_28831 < baseStart_28831 := by decide
  rcases family_descends (prefixWord ++ tailWord_28831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28888 : List Nat := [2, 1, 2, 2, 4, 1, 3, 4]
def baseStart_28888 : Nat := 118140960795 + 28888 * 2 ^ 59
def prefixEnd_28888 : Nat := 4983230072969 + 3 ^ 40 * 28888 * 2
def baseEnd_28888 : Nat := 8790180235370790676831

theorem tailTrace_28888 : CollatzResearch.WordTrace tailWord_28888 prefixEnd_28888 8790180235370790676831 := by
  unfold tailWord_28888
  simp only [CollatzResearch.WordTrace]
  refine ⟨526815959675592261359659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 702421279567456348479545 526815959675592261359659)
  ·
    refine ⟨790223939513388392039489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 526815959675592261359659 790223939513388392039489)
    ·
      refine ⟨592667954635041294029617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 790223939513388392039489 592667954635041294029617)
      ·
        refine ⟨444500965976280970522213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 592667954635041294029617 444500965976280970522213)
        ·
          refine ⟨83343931120552681972915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 444500965976280970522213 83343931120552681972915)
          ·
            refine ⟨125015896680829022959373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83343931120552681972915 125015896680829022959373)
            ·
              refine ⟨46880961255310883609765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125015896680829022959373 46880961255310883609765)
              ·
                refine ⟨8790180235370790676831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46880961255310883609765 8790180235370790676831)
                ·
                  rfl

theorem cell19_28888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 4].length) (baseStart_28888 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_28888 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_28888 prefixEnd_28888 := by exact prefixLift 28888
  have htrace : WordTrace (prefixWord ++ tailWord_28888) baseStart_28888 baseEnd_28888 := by
    simpa [prefixWord, tailWord_28888, baseEnd_28888] using wordTrace_append hprefix tailTrace_28888
  have hstable : (prefixWord ++ tailWord_28888).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28888).length < 2 ^ (prefixWord ++ tailWord_28888).sum := by decide
  have hdescent : baseEnd_28888 < baseStart_28888 := by decide
  rcases family_descends (prefixWord ++ tailWord_28888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28907 : List Nat := [1, 1, 1, 1, 2, 5, 5, 3]
def baseStart_28907 : Nat := 118140960795 + 28907 * 2 ^ 59
def prefixEnd_28907 : Nat := 4983230072969 + 3 ^ 40 * 28907 * 2
def baseEnd_28907 : Nat := 8795961647184376254557

theorem tailTrace_28907 : CollatzResearch.WordTrace tailWord_28907 prefixEnd_28907 8795961647184376254557 := by
  unfold tailWord_28907
  simp only [CollatzResearch.WordTrace]
  refine ⟨1054324906282350767660975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 702883270854900511773983 1054324906282350767660975)
  ·
    refine ⟨1581487359423526151491463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1054324906282350767660975 1581487359423526151491463)
    ·
      refine ⟨2372231039135289227237195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1581487359423526151491463 2372231039135289227237195)
      ·
        refine ⟨3558346558702933840855793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2372231039135289227237195 3558346558702933840855793)
        ·
          refine ⟨2668759919027200380641845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3558346558702933840855793 2668759919027200380641845)
          ·
            refine ⟨250196242408800035685173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2668759919027200380641845 250196242408800035685173)
            ·
              refine ⟨23455897725825003345485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 250196242408800035685173 23455897725825003345485)
              ·
                refine ⟨8795961647184376254557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23455897725825003345485 8795961647184376254557)
                ·
                  rfl

theorem cell19_28907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 3].length) (baseStart_28907 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_28907 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_28907 prefixEnd_28907 := by exact prefixLift 28907
  have htrace : WordTrace (prefixWord ++ tailWord_28907) baseStart_28907 baseEnd_28907 := by
    simpa [prefixWord, tailWord_28907, baseEnd_28907] using wordTrace_append hprefix tailTrace_28907
  have hstable : (prefixWord ++ tailWord_28907).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28907).length < 2 ^ (prefixWord ++ tailWord_28907).sum := by decide
  have hdescent : baseEnd_28907 < baseStart_28907 := by decide
  rcases family_descends (prefixWord ++ tailWord_28907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28926 : List Nat := [4, 2, 2, 1, 1, 1, 8]
def baseStart_28926 : Nat := 118140960795 + 28926 * 2 ^ 59
def prefixEnd_28926 : Nat := 4983230072969 + 3 ^ 40 * 28926 * 2
def baseEnd_28926 : Nat := 2933914352999320610761

theorem tailTrace_28926 : CollatzResearch.WordTrace tailWord_28926 prefixEnd_28926 2933914352999320610761 := by
  unfold tailWord_28926
  simp only [CollatzResearch.WordTrace]
  refine ⟨131877236651689626575329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 703345262142344675068421 131877236651689626575329)
  ·
    refine ⟨98907927488767219931497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131877236651689626575329 98907927488767219931497)
    ·
      refine ⟨74180945616575414948623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98907927488767219931497 74180945616575414948623)
      ·
        refine ⟨111271418424863122422935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74180945616575414948623 111271418424863122422935)
        ·
          refine ⟨166907127637294683634403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111271418424863122422935 166907127637294683634403)
          ·
            refine ⟨250360691455942025451605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166907127637294683634403 250360691455942025451605)
            ·
              refine ⟨2933914352999320610761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 250360691455942025451605 2933914352999320610761)
              ·
                rfl

theorem cell19_28926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 8].length) (baseStart_28926 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_28926 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_28926 prefixEnd_28926 := by exact prefixLift 28926
  have htrace : WordTrace (prefixWord ++ tailWord_28926) baseStart_28926 baseEnd_28926 := by
    simpa [prefixWord, tailWord_28926, baseEnd_28926] using wordTrace_append hprefix tailTrace_28926
  have hstable : (prefixWord ++ tailWord_28926).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28926).length < 2 ^ (prefixWord ++ tailWord_28926).sum := by decide
  have hdescent : baseEnd_28926 < baseStart_28926 := by decide
  rcases family_descends (prefixWord ++ tailWord_28926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28958 : List Nat := [4, 3, 2, 1, 1, 3, 2, 3]
def baseStart_28958 : Nat := 118140960795 + 28958 * 2 ^ 59
def prefixEnd_28958 : Nat := 4983230072969 + 3 ^ 40 * 28958 * 2
def baseEnd_28958 : Nat := 8811480173631369121085

theorem tailTrace_28958 : CollatzResearch.WordTrace tailWord_28958 prefixEnd_28958 8811480173631369121085 := by
  unfold tailWord_28958
  simp only [CollatzResearch.WordTrace]
  refine ⟨132023128637198309720941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 704123352731724318511685 132023128637198309720941)
  ·
    refine ⟨49508673238949366145353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132023128637198309720941 49508673238949366145353)
    ·
      refine ⟨37131504929212024609015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49508673238949366145353 37131504929212024609015)
      ·
        refine ⟨55697257393818036913523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37131504929212024609015 55697257393818036913523)
        ·
          refine ⟨83545886090727055370285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55697257393818036913523 83545886090727055370285)
          ·
            refine ⟨31329707284022645763857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83545886090727055370285 31329707284022645763857)
            ·
              refine ⟨23497280463016984322893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31329707284022645763857 23497280463016984322893)
              ·
                refine ⟨8811480173631369121085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23497280463016984322893 8811480173631369121085)
                ·
                  rfl

theorem cell19_28958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_28958 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_28958 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_28958 prefixEnd_28958 := by exact prefixLift 28958
  have htrace : WordTrace (prefixWord ++ tailWord_28958) baseStart_28958 baseEnd_28958 := by
    simpa [prefixWord, tailWord_28958, baseEnd_28958] using wordTrace_append hprefix tailTrace_28958
  have hstable : (prefixWord ++ tailWord_28958).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28958).length < 2 ^ (prefixWord ++ tailWord_28958).sum := by decide
  have hdescent : baseEnd_28958 < baseStart_28958 := by decide
  rcases family_descends (prefixWord ++ tailWord_28958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28962 : List Nat := [3, 3, 1, 1, 3, 1, 4, 3]
def baseStart_28962 : Nat := 118140960795 + 28962 * 2 ^ 59
def prefixEnd_28962 : Nat := 4983230072969 + 3 ^ 40 * 28962 * 2
def baseEnd_28962 : Nat := 8812697312960545032185

theorem tailTrace_28962 : CollatzResearch.WordTrace tailWord_28962 prefixEnd_28962 8812697312960545032185 := by
  unfold tailWord_28962
  simp only [CollatzResearch.WordTrace]
  refine ⟨264082730270773790228285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 704220614055396773942093 264082730270773790228285)
  ·
    refine ⟨99031023851540171335607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264082730270773790228285 99031023851540171335607)
    ·
      refine ⟨148546535777310257003411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99031023851540171335607 148546535777310257003411)
      ·
        refine ⟨222819803665965385505117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148546535777310257003411 222819803665965385505117)
        ·
          refine ⟨83557426374737019564419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222819803665965385505117 83557426374737019564419)
          ·
            refine ⟨125336139562105529346629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83557426374737019564419 125336139562105529346629)
            ·
              refine ⟨23500526167894786752493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125336139562105529346629 23500526167894786752493)
              ·
                refine ⟨8812697312960545032185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23500526167894786752493 8812697312960545032185)
                ·
                  rfl

theorem cell19_28962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 3].length) (baseStart_28962 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_28962 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_28962 prefixEnd_28962 := by exact prefixLift 28962
  have htrace : WordTrace (prefixWord ++ tailWord_28962) baseStart_28962 baseEnd_28962 := by
    simpa [prefixWord, tailWord_28962, baseEnd_28962] using wordTrace_append hprefix tailTrace_28962
  have hstable : (prefixWord ++ tailWord_28962).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28962).length < 2 ^ (prefixWord ++ tailWord_28962).sum := by decide
  have hdescent : baseEnd_28962 < baseStart_28962 := by decide
  rcases family_descends (prefixWord ++ tailWord_28962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28964 : List Nat := [2, 3, 1, 3, 1, 3, 1, 5]
def baseStart_28964 : Nat := 118140960795 + 28964 * 2 ^ 59
def prefixEnd_28964 : Nat := 4983230072969 + 3 ^ 40 * 28964 * 2
def baseEnd_28964 : Nat := 8813305882625132987735

theorem tailTrace_28964 : CollatzResearch.WordTrace tailWord_28964 prefixEnd_28964 8813305882625132987735 := by
  unfold tailWord_28964
  simp only [CollatzResearch.WordTrace]
  refine ⟨528201933537924751242973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 704269244717233001657297 528201933537924751242973)
  ·
    refine ⟨198075725076721781716115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 528201933537924751242973 198075725076721781716115)
    ·
      refine ⟨297113587615082672574173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198075725076721781716115 297113587615082672574173)
      ·
        refine ⟨111417595355656002215315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 297113587615082672574173 111417595355656002215315)
        ·
          refine ⟨167126393033484003322973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111417595355656002215315 167126393033484003322973)
          ·
            refine ⟨62672397387556501246115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167126393033484003322973 62672397387556501246115)
            ·
              refine ⟨94008596081334751869173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62672397387556501246115 94008596081334751869173)
              ·
                refine ⟨8813305882625132987735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94008596081334751869173 8813305882625132987735)
                ·
                  rfl

theorem cell19_28964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 5].length) (baseStart_28964 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_28964 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_28964 prefixEnd_28964 := by exact prefixLift 28964
  have htrace : WordTrace (prefixWord ++ tailWord_28964) baseStart_28964 baseEnd_28964 := by
    simpa [prefixWord, tailWord_28964, baseEnd_28964] using wordTrace_append hprefix tailTrace_28964
  have hstable : (prefixWord ++ tailWord_28964).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28964).length < 2 ^ (prefixWord ++ tailWord_28964).sum := by decide
  have hdescent : baseEnd_28964 < baseStart_28964 := by decide
  rcases family_descends (prefixWord ++ tailWord_28964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29023 : List Nat := [1, 1, 2, 3, 1, 2, 4, 5]
def baseStart_29023 : Nat := 118140960795 + 29023 * 2 ^ 59
def prefixEnd_29023 : Nat := 4983230072969 + 3 ^ 40 * 29023 * 2
def baseEnd_29023 : Nat := 8831258687730477676463

theorem tailTrace_29023 : CollatzResearch.WordTrace tailWord_29023 prefixEnd_29023 8831258687730477676463 := by
  unfold tailWord_29023
  simp only [CollatzResearch.WordTrace]
  refine ⟨1058555773862102578883723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 705703849241401719255815 1058555773862102578883723)
  ·
    refine ⟨1587833660793153868325585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1058555773862102578883723 1587833660793153868325585)
    ·
      refine ⟨1190875245594865401244189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1587833660793153868325585 1190875245594865401244189)
      ·
        refine ⟨446578217098074525466571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1190875245594865401244189 446578217098074525466571)
        ·
          refine ⟨669867325647111788199857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 446578217098074525466571 669867325647111788199857)
          ·
            refine ⟨502400494235333841149893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 669867325647111788199857 502400494235333841149893)
            ·
              refine ⟨94200092669125095215605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 502400494235333841149893 94200092669125095215605)
              ·
                refine ⟨8831258687730477676463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94200092669125095215605 8831258687730477676463)
                ·
                  rfl

theorem cell19_29023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 5].length) (baseStart_29023 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_29023 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_29023 prefixEnd_29023 := by exact prefixLift 29023
  have htrace : WordTrace (prefixWord ++ tailWord_29023) baseStart_29023 baseEnd_29023 := by
    simpa [prefixWord, tailWord_29023, baseEnd_29023] using wordTrace_append hprefix tailTrace_29023
  have hstable : (prefixWord ++ tailWord_29023).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29023).length < 2 ^ (prefixWord ++ tailWord_29023).sum := by decide
  have hdescent : baseEnd_29023 < baseStart_29023 := by decide
  rcases family_descends (prefixWord ++ tailWord_29023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29042 : List Nat := [3, 2, 1, 2, 1, 10]
def baseStart_29042 : Nat := 118140960795 + 29042 * 2 ^ 59
def prefixEnd_29042 : Nat := 4983230072969 + 3 ^ 40 * 29042 * 2
def baseEnd_29042 : Nat := 981893344393784806021

theorem tailTrace_29042 : CollatzResearch.WordTrace tailWord_29042 prefixEnd_29042 981893344393784806021 := by
  unfold tailWord_29042
  simp only [CollatzResearch.WordTrace]
  refine ⟨264812190198317205956345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 706165840528845882550253 264812190198317205956345)
  ·
    refine ⟨198609142648737904467259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264812190198317205956345 198609142648737904467259)
    ·
      refine ⟨297913713973106856700889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198609142648737904467259 297913713973106856700889)
      ·
        refine ⟨223435285479830142525667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297913713973106856700889 223435285479830142525667)
        ·
          refine ⟨335152928219745213788501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223435285479830142525667 335152928219745213788501)
          ·
            refine ⟨981893344393784806021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 335152928219745213788501 981893344393784806021)
            ·
              rfl

theorem cell19_29042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 10].length) (baseStart_29042 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_29042 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_29042 prefixEnd_29042 := by exact prefixLift 29042
  have htrace : WordTrace (prefixWord ++ tailWord_29042) baseStart_29042 baseEnd_29042 := by
    simpa [prefixWord, tailWord_29042, baseEnd_29042] using wordTrace_append hprefix tailTrace_29042
  have hstable : (prefixWord ++ tailWord_29042).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29042).length < 2 ^ (prefixWord ++ tailWord_29042).sum := by decide
  have hdescent : baseEnd_29042 < baseStart_29042 := by decide
  rcases family_descends (prefixWord ++ tailWord_29042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29057 : List Nat := [1, 2, 4, 3, 1, 3, 1, 4]
def baseStart_29057 : Nat := 118140960795 + 29057 * 2 ^ 59
def prefixEnd_29057 : Nat := 4983230072969 + 3 ^ 40 * 29057 * 2
def baseEnd_29057 : Nat := 8841604372028472920815

theorem tailTrace_29057 : CollatzResearch.WordTrace tailWord_29057 prefixEnd_29057 8841604372028472920815 := by
  unfold tailWord_29057
  simp only [CollatzResearch.WordTrace]
  refine ⟨1059795855738926385621425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 706530570492617590414283 1059795855738926385621425)
  ·
    refine ⟨794846891804194789216069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1059795855738926385621425 794846891804194789216069)
    ·
      refine ⟨149033792213286522978013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 794846891804194789216069 149033792213286522978013)
      ·
        refine ⟨55887672079982446116755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149033792213286522978013 55887672079982446116755)
        ·
          refine ⟨83831508119973669175133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55887672079982446116755 83831508119973669175133)
          ·
            refine ⟨31436815544990125940675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83831508119973669175133 31436815544990125940675)
            ·
              refine ⟨47155223317485188911013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31436815544990125940675 47155223317485188911013)
              ·
                refine ⟨8841604372028472920815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47155223317485188911013 8841604372028472920815)
                ·
                  rfl

theorem cell19_29057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 4].length) (baseStart_29057 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_29057 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_29057 prefixEnd_29057 := by exact prefixLift 29057
  have htrace : WordTrace (prefixWord ++ tailWord_29057) baseStart_29057 baseEnd_29057 := by
    simpa [prefixWord, tailWord_29057, baseEnd_29057] using wordTrace_append hprefix tailTrace_29057
  have hstable : (prefixWord ++ tailWord_29057).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29057).length < 2 ^ (prefixWord ++ tailWord_29057).sum := by decide
  have hdescent : baseEnd_29057 < baseStart_29057 := by decide
  rcases family_descends (prefixWord ++ tailWord_29057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29194 : List Nat := [3, 1, 2, 2, 2, 1, 1, 7]
def baseStart_29194 : Nat := 118140960795 + 29194 * 2 ^ 59
def prefixEnd_29194 : Nat := 4983230072969 + 3 ^ 40 * 29194 * 2
def baseEnd_29194 : Nat := 8883291394052747875997

theorem tailTrace_29194 : CollatzResearch.WordTrace tailWord_29194 prefixEnd_29194 8883291394052747875997 := by
  unfold tailWord_29194
  simp only [CollatzResearch.WordTrace]
  refine ⟨266198164060649695839659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 709861770828399188905757 266198164060649695839659)
  ·
    refine ⟨399297246090974543759489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266198164060649695839659 399297246090974543759489)
    ·
      refine ⟨299472934568230907819617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 399297246090974543759489 299472934568230907819617)
      ·
        refine ⟨224604700926173180864713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299472934568230907819617 224604700926173180864713)
        ·
          refine ⟨168453525694629885648535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224604700926173180864713 168453525694629885648535)
          ·
            refine ⟨252680288541944828472803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168453525694629885648535 252680288541944828472803)
            ·
              refine ⟨379020432812917242709205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252680288541944828472803 379020432812917242709205)
              ·
                refine ⟨8883291394052747875997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 379020432812917242709205 8883291394052747875997)
                ·
                  rfl

theorem cell19_29194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_29194 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_29194 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_29194 prefixEnd_29194 := by exact prefixLift 29194
  have htrace : WordTrace (prefixWord ++ tailWord_29194) baseStart_29194 baseEnd_29194 := by
    simpa [prefixWord, tailWord_29194, baseEnd_29194] using wordTrace_append hprefix tailTrace_29194
  have hstable : (prefixWord ++ tailWord_29194).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29194).length < 2 ^ (prefixWord ++ tailWord_29194).sum := by decide
  have hdescent : baseEnd_29194 < baseStart_29194 := by decide
  rcases family_descends (prefixWord ++ tailWord_29194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29213 : List Nat := [1, 4, 2, 2, 1, 9]
def baseStart_29213 : Nat := 118140960795 + 29213 * 2 ^ 59
def prefixEnd_29213 : Nat := 4983230072969 + 3 ^ 40 * 29213 * 2
def baseEnd_29213 : Nat := 987674756207370383747

theorem tailTrace_29213 : CollatzResearch.WordTrace tailWord_29213 prefixEnd_29213 987674756207370383747 := by
  unfold tailWord_29213
  simp only [CollatzResearch.WordTrace]
  refine ⟨1065485643173765028300293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 710323762115843352200195 1065485643173765028300293)
  ·
    refine ⟨199778558095080942806305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1065485643173765028300293 199778558095080942806305)
    ·
      refine ⟨149833918571310707104729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199778558095080942806305 149833918571310707104729)
      ·
        refine ⟨112375438928483030328547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149833918571310707104729 112375438928483030328547)
        ·
          refine ⟨168563158392724545492821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112375438928483030328547 168563158392724545492821)
          ·
            refine ⟨987674756207370383747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 168563158392724545492821 987674756207370383747)
            ·
              rfl

theorem cell19_29213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 9].length) (baseStart_29213 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_29213 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_29213 prefixEnd_29213 := by exact prefixLift 29213
  have htrace : WordTrace (prefixWord ++ tailWord_29213) baseStart_29213 baseEnd_29213 := by
    simpa [prefixWord, tailWord_29213, baseEnd_29213] using wordTrace_append hprefix tailTrace_29213
  have hstable : (prefixWord ++ tailWord_29213).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29213).length < 2 ^ (prefixWord ++ tailWord_29213).sum := by decide
  have hdescent : baseEnd_29213 < baseStart_29213 := by decide
  rcases family_descends (prefixWord ++ tailWord_29213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29232 : List Nat := [2, 1, 1, 1, 2, 3, 5, 4]
def baseStart_29232 : Nat := 118140960795 + 29232 * 2 ^ 59
def prefixEnd_29232 : Nat := 4983230072969 + 3 ^ 40 * 29232 * 2
def baseEnd_29232 : Nat := 8894854217679919031449

theorem tailTrace_29232 : CollatzResearch.WordTrace tailWord_29232 prefixEnd_29232 8894854217679919031449 := by
  unfold tailWord_29232
  simp only [CollatzResearch.WordTrace]
  refine ⟨533089315052465636620975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 710785753403287515494633 533089315052465636620975)
  ·
    refine ⟨799633972578698454931463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 533089315052465636620975 799633972578698454931463)
    ·
      refine ⟨1199450958868047682397195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 799633972578698454931463 1199450958868047682397195)
      ·
        refine ⟨1799176438302071523595793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1199450958868047682397195 1799176438302071523595793)
        ·
          refine ⟨1349382328726553642696845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1799176438302071523595793 1349382328726553642696845)
          ·
            refine ⟨506018373272457616011317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1349382328726553642696845 506018373272457616011317)
            ·
              refine ⟨47439222494292901501061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 506018373272457616011317 47439222494292901501061)
              ·
                refine ⟨8894854217679919031449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47439222494292901501061 8894854217679919031449)
                ·
                  rfl

theorem cell19_29232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 4].length) (baseStart_29232 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_29232 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_29232 prefixEnd_29232 := by exact prefixLift 29232
  have htrace : WordTrace (prefixWord ++ tailWord_29232) baseStart_29232 baseEnd_29232 := by
    simpa [prefixWord, tailWord_29232, baseEnd_29232] using wordTrace_append hprefix tailTrace_29232
  have hstable : (prefixWord ++ tailWord_29232).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29232).length < 2 ^ (prefixWord ++ tailWord_29232).sum := by decide
  have hdescent : baseEnd_29232 < baseStart_29232 := by decide
  rcases family_descends (prefixWord ++ tailWord_29232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29302 : List Nat := [5, 1, 1, 2, 3, 2, 2, 3]
def baseStart_29302 : Nat := 118140960795 + 29302 * 2 ^ 59
def prefixEnd_29302 : Nat := 4983230072969 + 3 ^ 40 * 29302 * 2
def baseEnd_29302 : Nat := 8916154155940497475703

theorem tailTrace_29302 : CollatzResearch.WordTrace tailWord_29302 prefixEnd_29302 8916154155940497475703 := by
  unfold tailWord_29302
  simp only [CollatzResearch.WordTrace]
  refine ⟨66795733740708326768135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 712487826567555485526773 66795733740708326768135)
  ·
    refine ⟨100193600611062490152203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66795733740708326768135 100193600611062490152203)
    ·
      refine ⟨150290400916593735228305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100193600611062490152203 150290400916593735228305)
      ·
        refine ⟨112717800687445301421229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150290400916593735228305 112717800687445301421229)
        ·
          refine ⟨42269175257791988032961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112717800687445301421229 42269175257791988032961)
          ·
            refine ⟨31701881443343991024721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42269175257791988032961 31701881443343991024721)
            ·
              refine ⟨23776411082507993268541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31701881443343991024721 23776411082507993268541)
              ·
                refine ⟨8916154155940497475703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23776411082507993268541 8916154155940497475703)
                ·
                  rfl

theorem cell19_29302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_29302 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_29302 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_29302 prefixEnd_29302 := by exact prefixLift 29302
  have htrace : WordTrace (prefixWord ++ tailWord_29302) baseStart_29302 baseEnd_29302 := by
    simpa [prefixWord, tailWord_29302, baseEnd_29302] using wordTrace_append hprefix tailTrace_29302
  have hstable : (prefixWord ++ tailWord_29302).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29302).length < 2 ^ (prefixWord ++ tailWord_29302).sum := by decide
  have hdescent : baseEnd_29302 < baseStart_29302 := by decide
  rcases family_descends (prefixWord ++ tailWord_29302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29344 : List Nat := [2, 1, 1, 4, 4, 1, 2, 4]
def baseStart_29344 : Nat := 118140960795 + 29344 * 2 ^ 59
def prefixEnd_29344 : Nat := 4983230072969 + 3 ^ 40 * 29344 * 2
def baseEnd_29344 : Nat := 8928934118896844542255

theorem tailTrace_29344 : CollatzResearch.WordTrace tailWord_29344 prefixEnd_29344 8928934118896844542255 := by
  unfold tailWord_29344
  simp only [CollatzResearch.WordTrace]
  refine ⟨535131802849587200659543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 713509070466116267546057 535131802849587200659543)
  ·
    refine ⟨802697704274380800989315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 535131802849587200659543 802697704274380800989315)
    ·
      refine ⟨1204046556411571201483973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 802697704274380800989315 1204046556411571201483973)
      ·
        refine ⟨225758729327169600278245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1204046556411571201483973 225758729327169600278245)
        ·
          refine ⟨42329761748844300052171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 225758729327169600278245 42329761748844300052171)
          ·
            refine ⟨63494642623266450078257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42329761748844300052171 63494642623266450078257)
            ·
              refine ⟨47620981967449837558693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63494642623266450078257 47620981967449837558693)
              ·
                refine ⟨8928934118896844542255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47620981967449837558693 8928934118896844542255)
                ·
                  rfl

theorem cell19_29344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 4].length) (baseStart_29344 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_29344 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_29344 prefixEnd_29344 := by exact prefixLift 29344
  have htrace : WordTrace (prefixWord ++ tailWord_29344) baseStart_29344 baseEnd_29344 := by
    simpa [prefixWord, tailWord_29344, baseEnd_29344] using wordTrace_append hprefix tailTrace_29344
  have hstable : (prefixWord ++ tailWord_29344).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29344).length < 2 ^ (prefixWord ++ tailWord_29344).sum := by decide
  have hdescent : baseEnd_29344 < baseStart_29344 := by decide
  rcases family_descends (prefixWord ++ tailWord_29344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29397 : List Nat := [1, 3, 2, 5, 2, 1, 1, 4]
def baseStart_29397 : Nat := 118140960795 + 29397 * 2 ^ 59
def prefixEnd_29397 : Nat := 4983230072969 + 3 ^ 40 * 29397 * 2
def baseEnd_29397 : Nat := 8945061215008425364333

theorem tailTrace_29397 : CollatzResearch.WordTrace tailWord_29397 prefixEnd_29397 8945061215008425364333 := by
  unfold tailWord_29397
  simp only [CollatzResearch.WordTrace]
  refine ⟨1072196674507164452998445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 714797783004776301998963 1072196674507164452998445)
  ·
    refine ⟨402073752940186669874417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1072196674507164452998445 402073752940186669874417)
    ·
      refine ⟨301555314705140002405813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402073752940186669874417 301555314705140002405813)
      ·
        refine ⟨28270810753606875225545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 301555314705140002405813 28270810753606875225545)
        ·
          refine ⟨21203108065205156419159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28270810753606875225545 21203108065205156419159)
          ·
            refine ⟨31804662097807734628739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21203108065205156419159 31804662097807734628739)
            ·
              refine ⟨47706993146711601943109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31804662097807734628739 47706993146711601943109)
              ·
                refine ⟨8945061215008425364333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47706993146711601943109 8945061215008425364333)
                ·
                  rfl

theorem cell19_29397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 4].length) (baseStart_29397 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_29397 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_29397 prefixEnd_29397 := by exact prefixLift 29397
  have htrace : WordTrace (prefixWord ++ tailWord_29397) baseStart_29397 baseEnd_29397 := by
    simpa [prefixWord, tailWord_29397, baseEnd_29397] using wordTrace_append hprefix tailTrace_29397
  have hstable : (prefixWord ++ tailWord_29397).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29397).length < 2 ^ (prefixWord ++ tailWord_29397).sum := by decide
  have hdescent : baseEnd_29397 < baseStart_29397 := by decide
  rcases family_descends (prefixWord ++ tailWord_29397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29481 : List Nat := [1, 2, 1, 1, 1, 1, 1, 11]
def baseStart_29481 : Nat := 118140960795 + 29481 * 2 ^ 59
def prefixEnd_29481 : Nat := 4983230072969 + 3 ^ 40 * 29481 * 2
def baseEnd_29481 : Nat := 8970621140921119497437

theorem tailTrace_29481 : CollatzResearch.WordTrace tailWord_29481 prefixEnd_29481 8970621140921119497437 := by
  unfold tailWord_29481
  simp only [CollatzResearch.WordTrace]
  refine ⟨1075260406202846799056297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 716840270801897866037531 1075260406202846799056297)
  ·
    refine ⟨806445304652135099292223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1075260406202846799056297 806445304652135099292223)
    ·
      refine ⟨1209667956978202648938335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 806445304652135099292223 1209667956978202648938335)
      ·
        refine ⟨1814501935467303973407503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1209667956978202648938335 1814501935467303973407503)
        ·
          refine ⟨2721752903200955960111255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1814501935467303973407503 2721752903200955960111255)
          ·
            refine ⟨4082629354801433940166883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2721752903200955960111255 4082629354801433940166883)
            ·
              refine ⟨6123944032202150910250325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4082629354801433940166883 6123944032202150910250325)
              ·
                refine ⟨8970621140921119497437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 6123944032202150910250325 8970621140921119497437)
                ·
                  rfl

theorem cell19_29481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 11].length) (baseStart_29481 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_29481 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_29481 prefixEnd_29481 := by exact prefixLift 29481
  have htrace : WordTrace (prefixWord ++ tailWord_29481) baseStart_29481 baseEnd_29481 := by
    simpa [prefixWord, tailWord_29481, baseEnd_29481] using wordTrace_append hprefix tailTrace_29481
  have hstable : (prefixWord ++ tailWord_29481).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29481).length < 2 ^ (prefixWord ++ tailWord_29481).sum := by decide
  have hdescent : baseEnd_29481 < baseStart_29481 := by decide
  rcases family_descends (prefixWord ++ tailWord_29481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29494 : List Nat := [5, 1, 2, 2, 2, 2, 5]
def baseStart_29494 : Nat := 118140960795 + 29494 * 2 ^ 59
def prefixEnd_29494 : Nat := 4983230072969 + 3 ^ 40 * 29494 * 2
def baseEnd_29494 : Nat := 2991525614580313736171

theorem tailTrace_29494 : CollatzResearch.WordTrace tailWord_29494 prefixEnd_29494 2991525614580313736171 := by
  unfold tailWord_29494
  simp only [CollatzResearch.WordTrace]
  refine ⟨67233409697234376204971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 717156370103833346186357 67233409697234376204971)
  ·
    refine ⟨100850114545851564307457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67233409697234376204971 100850114545851564307457)
    ·
      refine ⟨75637585909388673230593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100850114545851564307457 75637585909388673230593)
      ·
        refine ⟨56728189432041504922945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75637585909388673230593 56728189432041504922945)
        ·
          refine ⟨42546142074031128692209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56728189432041504922945 42546142074031128692209)
          ·
            refine ⟨31909606555523346519157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42546142074031128692209 31909606555523346519157)
            ·
              refine ⟨2991525614580313736171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31909606555523346519157 2991525614580313736171)
              ·
                rfl

theorem cell19_29494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 5].length) (baseStart_29494 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_29494 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_29494 prefixEnd_29494 := by exact prefixLift 29494
  have htrace : WordTrace (prefixWord ++ tailWord_29494) baseStart_29494 baseEnd_29494 := by
    simpa [prefixWord, tailWord_29494, baseEnd_29494] using wordTrace_append hprefix tailTrace_29494
  have hstable : (prefixWord ++ tailWord_29494).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29494).length < 2 ^ (prefixWord ++ tailWord_29494).sum := by decide
  have hdescent : baseEnd_29494 < baseStart_29494 := by decide
  rcases family_descends (prefixWord ++ tailWord_29494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29638 : List Nat := [6, 1, 3, 1, 2, 1, 2, 3]
def baseStart_29638 : Nat := 118140960795 + 29638 * 2 ^ 59
def prefixEnd_29638 : Nat := 4983230072969 + 3 ^ 40 * 29638 * 2
def baseEnd_29638 : Nat := 9018393859591274008121

theorem tailTrace_29638 : CollatzResearch.WordTrace tailWord_29638 prefixEnd_29638 9018393859591274008121 := by
  unfold tailWord_29638
  simp only [CollatzResearch.WordTrace]
  refine ⟨33780833332314456641299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 720657777756041741681045 33780833332314456641299)
  ·
    refine ⟨50671249998471684961949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33780833332314456641299 50671249998471684961949)
    ·
      refine ⟨19001718749426881860731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50671249998471684961949 19001718749426881860731)
      ·
        refine ⟨28502578124140322791097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19001718749426881860731 28502578124140322791097)
        ·
          refine ⟨21376933593105242093323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28502578124140322791097 21376933593105242093323)
          ·
            refine ⟨32065400389657863139985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21376933593105242093323 32065400389657863139985)
            ·
              refine ⟨24049050292243397354989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32065400389657863139985 24049050292243397354989)
              ·
                refine ⟨9018393859591274008121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24049050292243397354989 9018393859591274008121)
                ·
                  rfl

theorem cell19_29638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_29638 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_29638 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_29638 prefixEnd_29638 := by exact prefixLift 29638
  have htrace : WordTrace (prefixWord ++ tailWord_29638) baseStart_29638 baseEnd_29638 := by
    simpa [prefixWord, tailWord_29638, baseEnd_29638] using wordTrace_append hprefix tailTrace_29638
  have hstable : (prefixWord ++ tailWord_29638).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29638).length < 2 ^ (prefixWord ++ tailWord_29638).sum := by decide
  have hdescent : baseEnd_29638 < baseStart_29638 := by decide
  rcases family_descends (prefixWord ++ tailWord_29638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29686 : List Nat := [5, 1, 1, 1, 3, 2, 2, 4]
def baseStart_29686 : Nat := 118140960795 + 29686 * 2 ^ 59
def prefixEnd_29686 : Nat := 4983230072969 + 3 ^ 40 * 29686 * 2
def baseEnd_29686 : Nat := 9032999531541384941323

theorem tailTrace_29686 : CollatzResearch.WordTrace tailWord_29686 prefixEnd_29686 9032999531541384941323 := by
  unfold tailWord_29686
  simp only [CollatzResearch.WordTrace]
  refine ⟨67671085653760425641807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 721824913640111206845941 67671085653760425641807)
  ·
    refine ⟨101506628480640638462711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67671085653760425641807 101506628480640638462711)
    ·
      refine ⟨152259942720960957694067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101506628480640638462711 152259942720960957694067)
      ·
        refine ⟨228389914081441436541101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152259942720960957694067 228389914081441436541101)
        ·
          refine ⟨85646217780540538702913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228389914081441436541101 85646217780540538702913)
          ·
            refine ⟨64234663335405404027185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85646217780540538702913 64234663335405404027185)
            ·
              refine ⟨48175997501554053020389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64234663335405404027185 48175997501554053020389)
              ·
                refine ⟨9032999531541384941323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48175997501554053020389 9032999531541384941323)
                ·
                  rfl

theorem cell19_29686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_29686 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_29686 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_29686 prefixEnd_29686 := by exact prefixLift 29686
  have htrace : WordTrace (prefixWord ++ tailWord_29686) baseStart_29686 baseEnd_29686 := by
    simpa [prefixWord, tailWord_29686, baseEnd_29686] using wordTrace_append hprefix tailTrace_29686
  have hstable : (prefixWord ++ tailWord_29686).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29686).length < 2 ^ (prefixWord ++ tailWord_29686).sum := by decide
  have hdescent : baseEnd_29686 < baseStart_29686 := by decide
  rcases family_descends (prefixWord ++ tailWord_29686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29804 : List Nat := [2, 2, 1, 1, 3, 2, 2, 6]
def baseStart_29804 : Nat := 118140960795 + 29804 * 2 ^ 59
def prefixEnd_29804 : Nat := 4983230072969 + 3 ^ 40 * 29804 * 2
def baseEnd_29804 : Nat := 9068905141752074318779

theorem tailTrace_29804 : CollatzResearch.WordTrace tailWord_29804 prefixEnd_29804 9068905141752074318779 := by
  unfold tailWord_29804
  simp only [CollatzResearch.WordTrace]
  refine ⟨543520592016336481532233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 724694122688448642042977 543520592016336481532233)
  ·
    refine ⟨407640444012252361149175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 543520592016336481532233 407640444012252361149175)
    ·
      refine ⟨611460666018378541723763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407640444012252361149175 611460666018378541723763)
      ·
        refine ⟨917190999027567812585645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 611460666018378541723763 917190999027567812585645)
        ·
          refine ⟨343946624635337929719617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 917190999027567812585645 343946624635337929719617)
          ·
            refine ⟨257959968476503447289713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 343946624635337929719617 257959968476503447289713)
            ·
              refine ⟨193469976357377585467285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257959968476503447289713 193469976357377585467285)
              ·
                refine ⟨9068905141752074318779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 193469976357377585467285 9068905141752074318779)
                ·
                  rfl

theorem cell19_29804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 6].length) (baseStart_29804 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_29804 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_29804 prefixEnd_29804 := by exact prefixLift 29804
  have htrace : WordTrace (prefixWord ++ tailWord_29804) baseStart_29804 baseEnd_29804 := by
    simpa [prefixWord, tailWord_29804, baseEnd_29804] using wordTrace_append hprefix tailTrace_29804
  have hstable : (prefixWord ++ tailWord_29804).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29804).length < 2 ^ (prefixWord ++ tailWord_29804).sum := by decide
  have hdescent : baseEnd_29804 < baseStart_29804 := by decide
  rcases family_descends (prefixWord ++ tailWord_29804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29817 : List Nat := [1, 2, 1, 3, 6, 1, 2, 3]
def baseStart_29817 : Nat := 118140960795 + 29817 * 2 ^ 59
def prefixEnd_29817 : Nat := 4983230072969 + 3 ^ 40 * 29817 * 2
def baseEnd_29817 : Nat := 9072860844571896029855

theorem tailTrace_29817 : CollatzResearch.WordTrace tailWord_29817 prefixEnd_29817 9072860844571896029855 := by
  unfold tailWord_29817
  simp only [CollatzResearch.WordTrace]
  refine ⟨1087515332985576183287705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 725010221990384122191803 1087515332985576183287705)
  ·
    refine ⟨815636499739182137465779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1087515332985576183287705 815636499739182137465779)
    ·
      refine ⟨1223454749608773206198669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 815636499739182137465779 1223454749608773206198669)
      ·
        refine ⟨458795531103289952324501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1223454749608773206198669 458795531103289952324501)
        ·
          refine ⟨21506040520466716515211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 458795531103289952324501 21506040520466716515211)
          ·
            refine ⟨32259060780700074772817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21506040520466716515211 32259060780700074772817)
            ·
              refine ⟨24194295585525056079613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32259060780700074772817 24194295585525056079613)
              ·
                refine ⟨9072860844571896029855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24194295585525056079613 9072860844571896029855)
                ·
                  rfl

theorem cell19_29817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 3].length) (baseStart_29817 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_29817 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_29817 prefixEnd_29817 := by exact prefixLift 29817
  have htrace : WordTrace (prefixWord ++ tailWord_29817) baseStart_29817 baseEnd_29817 := by
    simpa [prefixWord, tailWord_29817, baseEnd_29817] using wordTrace_append hprefix tailTrace_29817
  have hstable : (prefixWord ++ tailWord_29817).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29817).length < 2 ^ (prefixWord ++ tailWord_29817).sum := by decide
  have hdescent : baseEnd_29817 < baseStart_29817 := by decide
  rcases family_descends (prefixWord ++ tailWord_29817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29861 : List Nat := [1, 3, 1, 2, 1, 4, 1, 6]
def baseStart_29861 : Nat := 118140960795 + 29861 * 2 ^ 59
def prefixEnd_29861 : Nat := 4983230072969 + 3 ^ 40 * 29861 * 2
def baseEnd_29861 : Nat := 9086249377192831051957

theorem tailTrace_29861 : CollatzResearch.WordTrace tailWord_29861 prefixEnd_29861 9086249377192831051957 := by
  unfold tailWord_29861
  simp only [CollatzResearch.WordTrace]
  refine ⟨1089120144826171697889437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 726080096550781131926291 1089120144826171697889437)
  ·
    refine ⟨408420054309814386708539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1089120144826171697889437 408420054309814386708539)
    ·
      refine ⟨612630081464721580062809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408420054309814386708539 612630081464721580062809)
      ·
        refine ⟨459472561098541185047107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 612630081464721580062809 459472561098541185047107)
        ·
          refine ⟨689208841647811777570661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459472561098541185047107 689208841647811777570661)
          ·
            refine ⟨129226657808964708294499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 689208841647811777570661 129226657808964708294499)
            ·
              refine ⟨193839986713447062441749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129226657808964708294499 193839986713447062441749)
              ·
                refine ⟨9086249377192831051957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 193839986713447062441749 9086249377192831051957)
                ·
                  rfl

theorem cell19_29861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 6].length) (baseStart_29861 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_29861 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_29861 prefixEnd_29861 := by exact prefixLift 29861
  have htrace : WordTrace (prefixWord ++ tailWord_29861) baseStart_29861 baseEnd_29861 := by
    simpa [prefixWord, tailWord_29861, baseEnd_29861] using wordTrace_append hprefix tailTrace_29861
  have hstable : (prefixWord ++ tailWord_29861).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29861).length < 2 ^ (prefixWord ++ tailWord_29861).sum := by decide
  have hdescent : baseEnd_29861 < baseStart_29861 := by decide
  rcases family_descends (prefixWord ++ tailWord_29861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29910 : List Nat := [5, 2, 1, 2, 3, 1, 1, 4]
def baseStart_29910 : Nat := 118140960795 + 29910 * 2 ^ 59
def prefixEnd_29910 : Nat := 4983230072969 + 3 ^ 40 * 29910 * 2
def baseEnd_29910 : Nat := 9101159333975235962935

theorem tailTrace_29910 : CollatzResearch.WordTrace tailWord_29910 prefixEnd_29910 9101159333975235962935 := by
  unfold tailWord_29910
  simp only [CollatzResearch.WordTrace]
  refine ⟨68181707603040816651449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 727271547765768710948789 68181707603040816651449)
  ·
    refine ⟨51136280702280612488587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68181707603040816651449 51136280702280612488587)
    ·
      refine ⟨76704421053420918732881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51136280702280612488587 76704421053420918732881)
      ·
        refine ⟨57528315790065689049661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76704421053420918732881 57528315790065689049661)
        ·
          refine ⟨21573118421274633393623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57528315790065689049661 21573118421274633393623)
          ·
            refine ⟨32359677631911950090435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21573118421274633393623 32359677631911950090435)
            ·
              refine ⟨48539516447867925135653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32359677631911950090435 48539516447867925135653)
              ·
                refine ⟨9101159333975235962935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48539516447867925135653 9101159333975235962935)
                ·
                  rfl

theorem cell19_29910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_29910 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_29910 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_29910 prefixEnd_29910 := by exact prefixLift 29910
  have htrace : WordTrace (prefixWord ++ tailWord_29910) baseStart_29910 baseEnd_29910 := by
    simpa [prefixWord, tailWord_29910, baseEnd_29910] using wordTrace_append hprefix tailTrace_29910
  have hstable : (prefixWord ++ tailWord_29910).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29910).length < 2 ^ (prefixWord ++ tailWord_29910).sum := by decide
  have hdescent : baseEnd_29910 < baseStart_29910 := by decide
  rcases family_descends (prefixWord ++ tailWord_29910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29933 : List Nat := [1, 5, 1, 2, 2, 2, 3, 3]
def baseStart_29933 : Nat := 118140960795 + 29933 * 2 ^ 59
def prefixEnd_29933 : Nat := 4983230072969 + 3 ^ 40 * 29933 * 2
def baseEnd_29933 : Nat := 9108157885117997451761

theorem tailTrace_29933 : CollatzResearch.WordTrace tailWord_29933 prefixEnd_29933 9108157885117997451761 := by
  unfold tailWord_29933
  simp only [CollatzResearch.WordTrace]
  refine ⟨1091746200565327994510453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 727830800376885329673635 1091746200565327994510453)
  ·
    refine ⟨102351206302999499485355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1091746200565327994510453 102351206302999499485355)
    ·
      refine ⟨153526809454499249228033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102351206302999499485355 153526809454499249228033)
      ·
        refine ⟨115145107090874436921025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153526809454499249228033 115145107090874436921025)
        ·
          refine ⟨86358830318155827690769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115145107090874436921025 86358830318155827690769)
          ·
            refine ⟨64769122738616870768077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86358830318155827690769 64769122738616870768077)
            ·
              refine ⟨24288421026981326538029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64769122738616870768077 24288421026981326538029)
              ·
                refine ⟨9108157885117997451761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24288421026981326538029 9108157885117997451761)
                ·
                  rfl

theorem cell19_29933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 3].length) (baseStart_29933 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_29933 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_29933 prefixEnd_29933 := by exact prefixLift 29933
  have htrace : WordTrace (prefixWord ++ tailWord_29933) baseStart_29933 baseEnd_29933 := by
    simpa [prefixWord, tailWord_29933, baseEnd_29933] using wordTrace_append hprefix tailTrace_29933
  have hstable : (prefixWord ++ tailWord_29933).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29933).length < 2 ^ (prefixWord ++ tailWord_29933).sum := by decide
  have hdescent : baseEnd_29933 < baseStart_29933 := by decide
  rcases family_descends (prefixWord ++ tailWord_29933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29975 : List Nat := [1, 1, 3, 4, 1, 1, 2, 6]
def baseStart_29975 : Nat := 118140960795 + 29975 * 2 ^ 59
def prefixEnd_29975 : Nat := 4983230072969 + 3 ^ 40 * 29975 * 2
def baseEnd_29975 : Nat := 9120937848074344518313

theorem tailTrace_29975 : CollatzResearch.WordTrace tailWord_29975 prefixEnd_29975 9120937848074344518313 := by
  unfold tailWord_29975
  simp only [CollatzResearch.WordTrace]
  refine ⟨1093278066413169167539379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 728852044275446111692919 1093278066413169167539379)
  ·
    refine ⟨1639917099619753751309069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1093278066413169167539379 1639917099619753751309069)
    ·
      refine ⟨614968912357407656740901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1639917099619753751309069 614968912357407656740901)
      ·
        refine ⟨115306671067013935638919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 614968912357407656740901 115306671067013935638919)
        ·
          refine ⟨172960006600520903458379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115306671067013935638919 172960006600520903458379)
          ·
            refine ⟨259440009900781355187569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172960006600520903458379 259440009900781355187569)
            ·
              refine ⟨194580007425586016390677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259440009900781355187569 194580007425586016390677)
              ·
                refine ⟨9120937848074344518313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 194580007425586016390677 9120937848074344518313)
                ·
                  rfl

theorem cell19_29975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 6].length) (baseStart_29975 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_29975 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_29975 prefixEnd_29975 := by exact prefixLift 29975
  have htrace : WordTrace (prefixWord ++ tailWord_29975) baseStart_29975 baseEnd_29975 := by
    simpa [prefixWord, tailWord_29975, baseEnd_29975] using wordTrace_append hprefix tailTrace_29975
  have hstable : (prefixWord ++ tailWord_29975).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29975).length < 2 ^ (prefixWord ++ tailWord_29975).sum := by decide
  have hdescent : baseEnd_29975 < baseStart_29975 := by decide
  rcases family_descends (prefixWord ++ tailWord_29975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29992 : List Nat := [2, 1, 5, 1, 2, 2, 1, 5]
def baseStart_29992 : Nat := 118140960795 + 29992 * 2 ^ 59
def prefixEnd_29992 : Nat := 4983230072969 + 3 ^ 40 * 29992 * 2
def baseEnd_29992 : Nat := 9126110690223342140489

theorem tailTrace_29992 : CollatzResearch.WordTrace tailWord_29992 prefixEnd_29992 9126110690223342140489 := by
  unfold tailWord_29992
  simp only [CollatzResearch.WordTrace]
  refine ⟨546949053675790535454115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 729265404901054047272153 546949053675790535454115)
  ·
    refine ⟨820423580513685803181173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 546949053675790535454115 820423580513685803181173)
    ·
      refine ⟨76914710673158044048235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 820423580513685803181173 76914710673158044048235)
      ·
        refine ⟨115372066009737066072353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76914710673158044048235 115372066009737066072353)
        ·
          refine ⟨86529049507302799554265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115372066009737066072353 86529049507302799554265)
          ·
            refine ⟨64896787130477099665699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86529049507302799554265 64896787130477099665699)
            ·
              refine ⟨97345180695715649498549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64896787130477099665699 97345180695715649498549)
              ·
                refine ⟨9126110690223342140489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97345180695715649498549 9126110690223342140489)
                ·
                  rfl

theorem cell19_29992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 5].length) (baseStart_29992 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_29992 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_29992 prefixEnd_29992 := by exact prefixLift 29992
  have htrace : WordTrace (prefixWord ++ tailWord_29992) baseStart_29992 baseEnd_29992 := by
    simpa [prefixWord, tailWord_29992, baseEnd_29992] using wordTrace_append hprefix tailTrace_29992
  have hstable : (prefixWord ++ tailWord_29992).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29992).length < 2 ^ (prefixWord ++ tailWord_29992).sum := by decide
  have hdescent : baseEnd_29992 < baseStart_29992 := by decide
  rcases family_descends (prefixWord ++ tailWord_29992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30009 : List Nat := [1, 2, 1, 6, 3, 1, 5]
def baseStart_30009 : Nat := 118140960795 + 30009 * 2 ^ 59
def prefixEnd_30009 : Nat := 4983230072969 + 3 ^ 40 * 30009 * 2
def baseEnd_30009 : Nat := 3043761177457446587555

theorem tailTrace_30009 : CollatzResearch.WordTrace tailWord_30009 prefixEnd_30009 3043761177457446587555 := by
  unfold tailWord_30009
  simp only [CollatzResearch.WordTrace]
  refine ⟨1094518148289992974277081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 729678765526661982851387 1094518148289992974277081)
  ·
    refine ⟨820888611217494730707811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1094518148289992974277081 820888611217494730707811)
    ·
      refine ⟨1231332916826242096061717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 820888611217494730707811 1231332916826242096061717)
      ·
        refine ⟨57718730476230098252893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1231332916826242096061717 57718730476230098252893)
        ·
          refine ⟨21644523928586286844835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57718730476230098252893 21644523928586286844835)
          ·
            refine ⟨32466785892879430267253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21644523928586286844835 32466785892879430267253)
            ·
              refine ⟨3043761177457446587555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32466785892879430267253 3043761177457446587555)
              ·
                rfl

theorem cell19_30009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 5].length) (baseStart_30009 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_30009 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_30009 prefixEnd_30009 := by exact prefixLift 30009
  have htrace : WordTrace (prefixWord ++ tailWord_30009) baseStart_30009 baseEnd_30009 := by
    simpa [prefixWord, tailWord_30009, baseEnd_30009] using wordTrace_append hprefix tailTrace_30009
  have hstable : (prefixWord ++ tailWord_30009).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30009).length < 2 ^ (prefixWord ++ tailWord_30009).sum := by decide
  have hdescent : baseEnd_30009 < baseStart_30009 := by decide
  rcases family_descends (prefixWord ++ tailWord_30009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan19Incremental
