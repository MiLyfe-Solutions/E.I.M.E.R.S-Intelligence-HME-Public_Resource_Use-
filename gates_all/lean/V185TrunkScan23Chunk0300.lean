import V185TrunkScan23Chunk0299

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1774313 : List Nat := [1, 2, 1, 1, 1, 2, 5, 2, 4, 1, 3]
def baseStart_1774313 : Nat := 118140960795 + 1774313 * 2 ^ 59
def prefixEnd_1774313 : Nat := 4983230072969 + 3 ^ 40 * 1774313 * 2
def baseEnd_1774313 : Nat := 911075400521021725927589

theorem tailTrace_1774313 : CollatzResearch.WordTrace tailWord_1774313 prefixEnd_1774313 911075400521021725927589 := by
  unfold tailWord_1774313
  simp only [CollatzResearch.WordTrace]
  refine ⟨64714511620974504380175593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43143007747316336253450395 64714511620974504380175593)
  ·
    refine ⟨48535883715730878285131695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64714511620974504380175593 48535883715730878285131695)
    ·
      refine ⟨72803825573596317427697543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48535883715730878285131695 72803825573596317427697543)
      ·
        refine ⟨109205738360394476141546315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72803825573596317427697543 109205738360394476141546315)
        ·
          refine ⟨163808607540591714212319473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109205738360394476141546315 163808607540591714212319473)
          ·
            refine ⟨122856455655443785659239605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163808607540591714212319473 122856455655443785659239605)
            ·
              refine ⟨11517792717697854905553713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 122856455655443785659239605 11517792717697854905553713)
              ·
                refine ⟨8638344538273391179165285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11517792717697854905553713 8638344538273391179165285)
                ·
                  refine ⟨1619689600926260846093491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8638344538273391179165285 1619689600926260846093491)
                  ·
                    refine ⟨2429534401389391269140237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1619689600926260846093491 2429534401389391269140237)
                    ·
                      refine ⟨911075400521021725927589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2429534401389391269140237 911075400521021725927589)
                      ·
                        rfl

theorem cell23_1774313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 4, 1, 3].length) (baseStart_1774313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1774313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1774313 prefixEnd_1774313 := by exact prefixLift 1774313
  have htrace : WordTrace (prefixWord ++ tailWord_1774313) baseStart_1774313 baseEnd_1774313 := by
    simpa [prefixWord, tailWord_1774313, baseEnd_1774313] using wordTrace_append hprefix tailTrace_1774313
  have hstable : (prefixWord ++ tailWord_1774313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774313).length < 2 ^ (prefixWord ++ tailWord_1774313).sum := by decide
  have hdescent : baseEnd_1774313 < baseStart_1774313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774323 : List Nat := [1, 1, 1, 2, 2, 3, 1, 2, 5, 3, 2]
def baseStart_1774323 : Nat := 118140960795 + 1774323 * 2 ^ 59
def prefixEnd_1774323 : Nat := 4983230072969 + 3 ^ 40 * 1774323 * 2
def baseEnd_1774323 : Nat := 911080535327566686802543

theorem tailTrace_1774323 : CollatzResearch.WordTrace tailWord_1774323 prefixEnd_1774323 911080535327566686802543 := by
  unfold tailWord_1774323
  simp only [CollatzResearch.WordTrace]
  refine ⟨64714876350938276088039623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43143250900625517392026415 64714876350938276088039623)
  ·
    refine ⟨97072314526407414132059435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64714876350938276088039623 97072314526407414132059435)
    ·
      refine ⟨145608471789611121198089153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97072314526407414132059435 145608471789611121198089153)
      ·
        refine ⟨109206353842208340898566865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145608471789611121198089153 109206353842208340898566865)
        ·
          refine ⟨81904765381656255673925149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109206353842208340898566865 81904765381656255673925149)
          ·
            refine ⟨30714287018121095877721931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81904765381656255673925149 30714287018121095877721931)
            ·
              refine ⟨46071430527181643816582897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30714287018121095877721931 46071430527181643816582897)
              ·
                refine ⟨34553572895386232862437173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46071430527181643816582897 34553572895386232862437173)
                ·
                  refine ⟨3239397458942459330853485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34553572895386232862437173 3239397458942459330853485)
                  ·
                    refine ⟨1214774047103422249070057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3239397458942459330853485 1214774047103422249070057)
                    ·
                      refine ⟨911080535327566686802543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1214774047103422249070057 911080535327566686802543)
                      ·
                        rfl

theorem cell23_1774323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 5, 3, 2].length) (baseStart_1774323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1774323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1774323 prefixEnd_1774323 := by exact prefixLift 1774323
  have htrace : WordTrace (prefixWord ++ tailWord_1774323) baseStart_1774323 baseEnd_1774323 := by
    simpa [prefixWord, tailWord_1774323, baseEnd_1774323] using wordTrace_append hprefix tailTrace_1774323
  have hstable : (prefixWord ++ tailWord_1774323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774323).length < 2 ^ (prefixWord ++ tailWord_1774323).sum := by decide
  have hdescent : baseEnd_1774323 < baseStart_1774323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774340 : List Nat := [2, 3, 2, 2, 1, 1, 2, 2, 3, 3, 2]
def baseStart_1774340 : Nat := 118140960795 + 1774340 * 2 ^ 59
def prefixEnd_1774340 : Nat := 4983230072969 + 3 ^ 40 * 1774340 * 2
def baseEnd_1774340 : Nat := 911089264498693120289965

theorem tailTrace_1774340 : CollatzResearch.WordTrace tailWord_1774340 prefixEnd_1774340 911089264498693120289965 := by
  unfold tailWord_1774340
  simp only [CollatzResearch.WordTrace]
  refine ⟨32357748195938343995704237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43143664261251125327605649 32357748195938343995704237)
  ·
    refine ⟨12134155573476878998389089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32357748195938343995704237 12134155573476878998389089)
    ·
      refine ⟨9100616680107659248791817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12134155573476878998389089 9100616680107659248791817)
      ·
        refine ⟨6825462510080744436593863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9100616680107659248791817 6825462510080744436593863)
        ·
          refine ⟨10238193765121116654890795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6825462510080744436593863 10238193765121116654890795)
          ·
            refine ⟨15357290647681674982336193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10238193765121116654890795 15357290647681674982336193)
            ·
              refine ⟨11517967985761256236752145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15357290647681674982336193 11517967985761256236752145)
              ·
                refine ⟨8638475989320942177564109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11517967985761256236752145 8638475989320942177564109)
                ·
                  refine ⟨3239428495995353316586541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8638475989320942177564109 3239428495995353316586541)
                  ·
                    refine ⟨1214785685998257493719953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3239428495995353316586541 1214785685998257493719953)
                    ·
                      refine ⟨911089264498693120289965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1214785685998257493719953 911089264498693120289965)
                      ·
                        rfl

theorem cell23_1774340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_1774340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1774340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1774340 prefixEnd_1774340 := by exact prefixLift 1774340
  have htrace : WordTrace (prefixWord ++ tailWord_1774340) baseStart_1774340 baseEnd_1774340 := by
    simpa [prefixWord, tailWord_1774340, baseEnd_1774340] using wordTrace_append hprefix tailTrace_1774340
  have hstable : (prefixWord ++ tailWord_1774340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774340).length < 2 ^ (prefixWord ++ tailWord_1774340).sum := by decide
  have hdescent : baseEnd_1774340 < baseStart_1774340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774346 : List Nat := [3, 1, 2, 2, 1, 2, 2, 1, 1, 8]
def baseStart_1774346 : Nat := 118140960795 + 1774346 * 2 ^ 59
def prefixEnd_1774346 : Nat := 4983230072969 + 3 ^ 40 * 1774346 * 2
def baseEnd_1774346 : Nat := 303697448460873365604979

theorem tailTrace_1774346 : CollatzResearch.WordTrace tailWord_1774346 prefixEnd_1774346 303697448460873365604979 := by
  unfold tailWord_1774346
  simp only [CollatzResearch.WordTrace]
  refine ⟨16178928807463737754031723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43143810153236634010751261 16178928807463737754031723)
  ·
    refine ⟨24268393211195606631047585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16178928807463737754031723 24268393211195606631047585)
    ·
      refine ⟨18201294908396704973285689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24268393211195606631047585 18201294908396704973285689)
      ·
        refine ⟨13650971181297528729964267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18201294908396704973285689 13650971181297528729964267)
        ·
          refine ⟨20476456771946293094946401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13650971181297528729964267 20476456771946293094946401)
          ·
            refine ⟨15357342578959719821209801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20476456771946293094946401 15357342578959719821209801)
            ·
              refine ⟨11518006934219789865907351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15357342578959719821209801 11518006934219789865907351)
              ·
                refine ⟨17277010401329684798861027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11518006934219789865907351 17277010401329684798861027)
                ·
                  refine ⟨25915515601994527198291541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17277010401329684798861027 25915515601994527198291541)
                  ·
                    refine ⟨303697448460873365604979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 25915515601994527198291541 303697448460873365604979)
                    ·
                      rfl

theorem cell23_1774346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 1, 8].length) (baseStart_1774346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1774346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1774346 prefixEnd_1774346 := by exact prefixLift 1774346
  have htrace : WordTrace (prefixWord ++ tailWord_1774346) baseStart_1774346 baseEnd_1774346 := by
    simpa [prefixWord, tailWord_1774346, baseEnd_1774346] using wordTrace_append hprefix tailTrace_1774346
  have hstable : (prefixWord ++ tailWord_1774346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774346).length < 2 ^ (prefixWord ++ tailWord_1774346).sum := by decide
  have hdescent : baseEnd_1774346 < baseStart_1774346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774370 : List Nat := [3, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2]
def baseStart_1774370 : Nat := 118140960795 + 1774370 * 2 ^ 59
def prefixEnd_1774370 : Nat := 4983230072969 + 3 ^ 40 * 1774370 * 2
def baseEnd_1774370 : Nat := 911104668918328002914827

theorem tailTrace_1774370 : CollatzResearch.WordTrace tailWord_1774370 prefixEnd_1774370 911104668918328002914827 := by
  unfold tailWord_1774370
  simp only [CollatzResearch.WordTrace]
  refine ⟨16179147645442000778750141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43144393721178668743333709 16179147645442000778750141)
  ·
    refine ⟨6067180367040750292031303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16179147645442000778750141 6067180367040750292031303)
    ·
      refine ⟨9100770550561125438046955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6067180367040750292031303 9100770550561125438046955)
      ·
        refine ⟨13651155825841688157070433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9100770550561125438046955 13651155825841688157070433)
        ·
          refine ⟨10238366869381266117802825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13651155825841688157070433 10238366869381266117802825)
          ·
            refine ⟨7678775152035949588352119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10238366869381266117802825 7678775152035949588352119)
            ·
              refine ⟨11518162728053924382528179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7678775152035949588352119 11518162728053924382528179)
              ·
                refine ⟨17277244092080886573792269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11518162728053924382528179 17277244092080886573792269)
                ·
                  refine ⟨6478966534530332465172101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17277244092080886573792269 6478966534530332465172101)
                  ·
                    refine ⟨1214806225224437337219769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6478966534530332465172101 1214806225224437337219769)
                    ·
                      refine ⟨911104668918328002914827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1214806225224437337219769 911104668918328002914827)
                      ·
                        rfl

theorem cell23_1774370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2].length) (baseStart_1774370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1774370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1774370 prefixEnd_1774370 := by exact prefixLift 1774370
  have htrace : WordTrace (prefixWord ++ tailWord_1774370) baseStart_1774370 baseEnd_1774370 := by
    simpa [prefixWord, tailWord_1774370, baseEnd_1774370] using wordTrace_append hprefix tailTrace_1774370
  have hstable : (prefixWord ++ tailWord_1774370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774370).length < 2 ^ (prefixWord ++ tailWord_1774370).sum := by decide
  have hdescent : baseEnd_1774370 < baseStart_1774370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774381 : List Nat := [1, 5, 3, 2, 1, 1, 2, 2, 2, 1, 3]
def baseStart_1774381 : Nat := 118140960795 + 1774381 * 2 ^ 59
def prefixEnd_1774381 : Nat := 4983230072969 + 3 ^ 40 * 1774381 * 2
def baseEnd_1774381 : Nat := 911110317205527459877277

theorem tailTrace_1774381 : CollatzResearch.WordTrace tailWord_1774381 prefixEnd_1774381 911110317205527459877277 := by
  unfold tailWord_1774381
  simp only [CollatzResearch.WordTrace]
  refine ⟨64716991784728151993650997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43144661189818767995767331 64716991784728151993650997)
  ·
    refine ⟨6067217979818264249404781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64716991784728151993650997 6067217979818264249404781)
    ·
      refine ⟨2275206742431849093526793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6067217979818264249404781 2275206742431849093526793)
      ·
        refine ⟨1706405056823886820145095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2275206742431849093526793 1706405056823886820145095)
        ·
          refine ⟨2559607585235830230217643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1706405056823886820145095 2559607585235830230217643)
          ·
            refine ⟨3839411377853745345326465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2559607585235830230217643 3839411377853745345326465)
            ·
              refine ⟨2879558533390309008994849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3839411377853745345326465 2879558533390309008994849)
              ·
                refine ⟨2159668900042731756746137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2879558533390309008994849 2159668900042731756746137)
                ·
                  refine ⟨1619751675032048817559603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2159668900042731756746137 1619751675032048817559603)
                  ·
                    refine ⟨2429627512548073226339405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1619751675032048817559603 2429627512548073226339405)
                    ·
                      refine ⟨911110317205527459877277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2429627512548073226339405 911110317205527459877277)
                      ·
                        rfl

theorem cell23_1774381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_1774381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1774381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1774381 prefixEnd_1774381 := by exact prefixLift 1774381
  have htrace : WordTrace (prefixWord ++ tailWord_1774381) baseStart_1774381 baseEnd_1774381 := by
    simpa [prefixWord, tailWord_1774381, baseEnd_1774381] using wordTrace_append hprefix tailTrace_1774381
  have hstable : (prefixWord ++ tailWord_1774381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774381).length < 2 ^ (prefixWord ++ tailWord_1774381).sum := by decide
  have hdescent : baseEnd_1774381 < baseStart_1774381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774387 : List Nat := [1, 1, 1, 2, 6, 1, 1, 4, 2, 2, 2]
def baseStart_1774387 : Nat := 118140960795 + 1774387 * 2 ^ 59
def prefixEnd_1774387 : Nat := 4983230072969 + 3 ^ 40 * 1774387 * 2
def baseEnd_1774387 : Nat := 911113398089454436402249

theorem tailTrace_1774387 : CollatzResearch.WordTrace tailWord_1774387 prefixEnd_1774387 911113398089454436402249 := by
  unfold tailWord_1774387
  simp only [CollatzResearch.WordTrace]
  refine ⟨64717210622706415018369415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43144807081804276678912943 64717210622706415018369415)
  ·
    refine ⟨97075815934059622527554123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64717210622706415018369415 97075815934059622527554123)
    ·
      refine ⟨145613723901089433791331185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97075815934059622527554123 145613723901089433791331185)
      ·
        refine ⟨109210292925817075343498389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145613723901089433791331185 109210292925817075343498389)
        ·
          refine ⟨5119232480897675406726487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 109210292925817075343498389 5119232480897675406726487)
          ·
            refine ⟨7678848721346513110089731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5119232480897675406726487 7678848721346513110089731)
            ·
              refine ⟨11518273082019769665134597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7678848721346513110089731 11518273082019769665134597)
              ·
                refine ⟨2159676202878706812212737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11518273082019769665134597 2159676202878706812212737)
                ·
                  refine ⟨1619757152159030109159553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2159676202878706812212737 1619757152159030109159553)
                  ·
                    refine ⟨1214817864119272581869665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1619757152159030109159553 1214817864119272581869665)
                    ·
                      refine ⟨911113398089454436402249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1214817864119272581869665 911113398089454436402249)
                      ·
                        rfl

theorem cell23_1774387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 4, 2, 2, 2].length) (baseStart_1774387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1774387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1774387 prefixEnd_1774387 := by exact prefixLift 1774387
  have htrace : WordTrace (prefixWord ++ tailWord_1774387) baseStart_1774387 baseEnd_1774387 := by
    simpa [prefixWord, tailWord_1774387, baseEnd_1774387] using wordTrace_append hprefix tailTrace_1774387
  have hstable : (prefixWord ++ tailWord_1774387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774387).length < 2 ^ (prefixWord ++ tailWord_1774387).sum := by decide
  have hdescent : baseEnd_1774387 < baseStart_1774387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774396 : List Nat := [2, 2, 2, 2, 1, 1, 1, 1, 2, 1, 8]
def baseStart_1774396 : Nat := 118140960795 + 1774396 * 2 ^ 59
def prefixEnd_1774396 : Nat := 4983230072969 + 3 ^ 40 * 1774396 * 2
def baseEnd_1774396 : Nat := 911118019415344901189707

theorem tailTrace_1774396 : CollatzResearch.WordTrace tailWord_1774396 prefixEnd_1774396 911118019415344901189707 := by
  unfold tailWord_1774396
  simp only [CollatzResearch.WordTrace]
  refine ⟨32358769439836904777723521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43145025919782539703631361 32358769439836904777723521)
  ·
    refine ⟨24269077079877678583292641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32358769439836904777723521 24269077079877678583292641)
    ·
      refine ⟨18201807809908258937469481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24269077079877678583292641 18201807809908258937469481)
      ·
        refine ⟨13651355857431194203102111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18201807809908258937469481 13651355857431194203102111)
        ·
          refine ⟨20477033786146791304653167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13651355857431194203102111 20477033786146791304653167)
          ·
            refine ⟨30715550679220186956979751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20477033786146791304653167 30715550679220186956979751)
            ·
              refine ⟨46073326018830280435469627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30715550679220186956979751 46073326018830280435469627)
              ·
                refine ⟨69109989028245420653204441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46073326018830280435469627 69109989028245420653204441)
                ·
                  refine ⟨51832491771184065489903331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69109989028245420653204441 51832491771184065489903331)
                  ·
                    refine ⟨77748737656776098234854997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51832491771184065489903331 77748737656776098234854997)
                    ·
                      refine ⟨911118019415344901189707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 77748737656776098234854997 911118019415344901189707)
                      ·
                        rfl

theorem cell23_1774396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_1774396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1774396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1774396 prefixEnd_1774396 := by exact prefixLift 1774396
  have htrace : WordTrace (prefixWord ++ tailWord_1774396) baseStart_1774396 baseEnd_1774396 := by
    simpa [prefixWord, tailWord_1774396, baseEnd_1774396] using wordTrace_append hprefix tailTrace_1774396
  have hstable : (prefixWord ++ tailWord_1774396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774396).length < 2 ^ (prefixWord ++ tailWord_1774396).sum := by decide
  have hdescent : baseEnd_1774396 < baseStart_1774396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774403 : List Nat := [1, 1, 1, 3, 1, 4, 3, 1, 2, 3, 3]
def baseStart_1774403 : Nat := 118140960795 + 1774403 * 2 ^ 59
def prefixEnd_1774403 : Nat := 4983230072969 + 3 ^ 40 * 1774403 * 2
def baseEnd_1774403 : Nat := 911121613779926373802175

theorem tailTrace_1774403 : CollatzResearch.WordTrace tailWord_1774403 prefixEnd_1774403 911121613779926373802175 := by
  unfold tailWord_1774403
  simp only [CollatzResearch.WordTrace]
  refine ⟨64717794190648449750951863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43145196127098966500634575 64717794190648449750951863)
  ·
    refine ⟨97076691285972674626427795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64717794190648449750951863 97076691285972674626427795)
    ·
      refine ⟨145615036928959011939641693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97076691285972674626427795 145615036928959011939641693)
      ·
        refine ⟨54605638848359629477365635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145615036928959011939641693 54605638848359629477365635)
        ·
          refine ⟨81908458272539444216048453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54605638848359629477365635 81908458272539444216048453)
          ·
            refine ⟨15357835926101145790509085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81908458272539444216048453 15357835926101145790509085)
            ·
              refine ⟨5759188472287929671440907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15357835926101145790509085 5759188472287929671440907)
              ·
                refine ⟨8638782708431894507161361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5759188472287929671440907 8638782708431894507161361)
                ·
                  refine ⟨6479087031323920880371021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8638782708431894507161361 6479087031323920880371021)
                  ·
                    refine ⟨2429657636746470330139133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6479087031323920880371021 2429657636746470330139133)
                    ·
                      refine ⟨911121613779926373802175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2429657636746470330139133 911121613779926373802175)
                      ·
                        rfl

theorem cell23_1774403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 2, 3, 3].length) (baseStart_1774403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1774403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1774403 prefixEnd_1774403 := by exact prefixLift 1774403
  have htrace : WordTrace (prefixWord ++ tailWord_1774403) baseStart_1774403 baseEnd_1774403 := by
    simpa [prefixWord, tailWord_1774403, baseEnd_1774403] using wordTrace_append hprefix tailTrace_1774403
  have hstable : (prefixWord ++ tailWord_1774403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774403).length < 2 ^ (prefixWord ++ tailWord_1774403).sum := by decide
  have hdescent : baseEnd_1774403 < baseStart_1774403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774416 : List Nat := [2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 7]
def baseStart_1774416 : Nat := 118140960795 + 1774416 * 2 ^ 59
def prefixEnd_1774416 : Nat := 4983230072969 + 3 ^ 40 * 1774416 * 2
def baseEnd_1774416 : Nat := 911128289028434822939615

theorem tailTrace_1774416 : CollatzResearch.WordTrace tailWord_1774416 prefixEnd_1774416 911128289028434822939615 := by
  unfold tailWord_1774416
  simp only [CollatzResearch.WordTrace]
  refine ⟨32359134169800676485587551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43145512226400901980783401 32359134169800676485587551)
  ·
    refine ⟨48538701254701014728381327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32359134169800676485587551 48538701254701014728381327)
    ·
      refine ⟨72808051882051522092571991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48538701254701014728381327 72808051882051522092571991)
      ·
        refine ⟨109212077823077283138857987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72808051882051522092571991 109212077823077283138857987)
        ·
          refine ⟨163818116734615924708286981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109212077823077283138857987 163818116734615924708286981)
          ·
            refine ⟨30715896887740485882803809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 163818116734615924708286981 30715896887740485882803809)
            ·
              refine ⟨23036922665805364412102857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30715896887740485882803809 23036922665805364412102857)
              ·
                refine ⟨17277691999354023309077143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23036922665805364412102857 17277691999354023309077143)
                ·
                  refine ⟨25916537999031034963615715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17277691999354023309077143 25916537999031034963615715)
                  ·
                    refine ⟨38874806998546552445423573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25916537999031034963615715 38874806998546552445423573)
                    ·
                      refine ⟨911128289028434822939615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 38874806998546552445423573 911128289028434822939615)
                      ·
                        rfl

theorem cell23_1774416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 7].length) (baseStart_1774416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1774416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1774416 prefixEnd_1774416 := by exact prefixLift 1774416
  have htrace : WordTrace (prefixWord ++ tailWord_1774416) baseStart_1774416 baseEnd_1774416 := by
    simpa [prefixWord, tailWord_1774416, baseEnd_1774416] using wordTrace_append hprefix tailTrace_1774416
  have hstable : (prefixWord ++ tailWord_1774416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774416).length < 2 ^ (prefixWord ++ tailWord_1774416).sum := by decide
  have hdescent : baseEnd_1774416 < baseStart_1774416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774423 : List Nat := [1, 1, 3, 2, 4, 2, 1, 1, 1, 7]
def baseStart_1774423 : Nat := 118140960795 + 1774423 * 2 ^ 59
def prefixEnd_1774423 : Nat := 4983230072969 + 3 ^ 40 * 1774423 * 2
def baseEnd_1774423 : Nat := 303710627797672098517361

theorem tailTrace_1774423 : CollatzResearch.WordTrace tailWord_1774423 prefixEnd_1774423 303710627797672098517361 := by
  unfold tailWord_1774423
  simp only [CollatzResearch.WordTrace]
  refine ⟨64718523650575993166679923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43145682433717328777786615 64718523650575993166679923)
  ·
    refine ⟨97077785475863989750019885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64718523650575993166679923 97077785475863989750019885)
    ·
      refine ⟨36404169553448996156257457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97077785475863989750019885 36404169553448996156257457)
      ·
        refine ⟨27303127165086747117193093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36404169553448996156257457 27303127165086747117193093)
        ·
          refine ⟨5119336343453765084473705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27303127165086747117193093 5119336343453765084473705)
          ·
            refine ⟨3839502257590323813355279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5119336343453765084473705 3839502257590323813355279)
            ·
              refine ⟨5759253386385485720032919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3839502257590323813355279 5759253386385485720032919)
              ·
                refine ⟨8638880079578228580049379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5759253386385485720032919 8638880079578228580049379)
                ·
                  refine ⟨12958320119367342870074069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8638880079578228580049379 12958320119367342870074069)
                  ·
                    refine ⟨303710627797672098517361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12958320119367342870074069 303710627797672098517361)
                    ·
                      rfl

theorem cell23_1774423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 7].length) (baseStart_1774423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1774423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1774423 prefixEnd_1774423 := by exact prefixLift 1774423
  have htrace : WordTrace (prefixWord ++ tailWord_1774423) baseStart_1774423 baseEnd_1774423 := by
    simpa [prefixWord, tailWord_1774423, baseEnd_1774423] using wordTrace_append hprefix tailTrace_1774423
  have hstable : (prefixWord ++ tailWord_1774423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774423).length < 2 ^ (prefixWord ++ tailWord_1774423).sum := by decide
  have hdescent : baseEnd_1774423 < baseStart_1774423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774443 : List Nat := [1, 1, 1, 1, 2, 2, 4, 4, 2, 1, 4]
def baseStart_1774443 : Nat := 118140960795 + 1774443 * 2 ^ 59
def prefixEnd_1774443 : Nat := 4983230072969 + 3 ^ 40 * 1774443 * 2
def baseEnd_1774443 : Nat := 911142153006106217301991

theorem tailTrace_1774443 : CollatzResearch.WordTrace tailWord_1774443 prefixEnd_1774443 911142153006106217301991 := by
  unfold tailWord_1774443
  simp only [CollatzResearch.WordTrace]
  refine ⟨64719253110503536582407983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43146168740335691054938655 64719253110503536582407983)
  ·
    refine ⟨97078879665755304873611975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64719253110503536582407983 97078879665755304873611975)
    ·
      refine ⟨145618319498632957310417963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97078879665755304873611975 145618319498632957310417963)
      ·
        refine ⟨218427479247949435965626945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145618319498632957310417963 218427479247949435965626945)
        ·
          refine ⟨163820609435962076974220209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218427479247949435965626945 163820609435962076974220209)
          ·
            refine ⟨122865457076971557730665157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163820609435962076974220209 122865457076971557730665157)
            ·
              refine ⟨23037273201932167074499717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122865457076971557730665157 23037273201932167074499717)
              ·
                refine ⟨4319488725362281326468697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23037273201932167074499717 4319488725362281326468697)
                ·
                  refine ⟨3239616544021710994851523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4319488725362281326468697 3239616544021710994851523)
                  ·
                    refine ⟨4859424816032566492277285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3239616544021710994851523 4859424816032566492277285)
                    ·
                      refine ⟨911142153006106217301991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4859424816032566492277285 911142153006106217301991)
                      ·
                        rfl

theorem cell23_1774443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 2, 1, 4].length) (baseStart_1774443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1774443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1774443 prefixEnd_1774443 := by exact prefixLift 1774443
  have htrace : WordTrace (prefixWord ++ tailWord_1774443) baseStart_1774443 baseEnd_1774443 := by
    simpa [prefixWord, tailWord_1774443, baseEnd_1774443] using wordTrace_append hprefix tailTrace_1774443
  have hstable : (prefixWord ++ tailWord_1774443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774443).length < 2 ^ (prefixWord ++ tailWord_1774443).sum := by decide
  have hdescent : baseEnd_1774443 < baseStart_1774443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774463 : List Nat := [1, 1, 2, 2, 1, 1, 5, 2, 1, 4, 3]
def baseStart_1774463 : Nat := 118140960795 + 1774463 * 2 ^ 59
def prefixEnd_1774463 : Nat := 4983230072969 + 3 ^ 40 * 1774463 * 2
def baseEnd_1774463 : Nat := 911152422619196139051899

theorem tailTrace_1774463 : CollatzResearch.WordTrace tailWord_1774463 prefixEnd_1774463 911152422619196139051899 := by
  unfold tailWord_1774463
  simp only [CollatzResearch.WordTrace]
  refine ⟨64719982570431079998136043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43146655046954053332090695 64719982570431079998136043)
  ·
    refine ⟨97079973855646619997204065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64719982570431079998136043 97079973855646619997204065)
    ·
      refine ⟨72809980391734964997903049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97079973855646619997204065 72809980391734964997903049)
      ·
        refine ⟨54607485293801223748427287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72809980391734964997903049 54607485293801223748427287)
        ·
          refine ⟨81911227940701835622640931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54607485293801223748427287 81911227940701835622640931)
          ·
            refine ⟨122866841911052753433961397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81911227940701835622640931 122866841911052753433961397)
            ·
              refine ⟨11518766429161195634433881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 122866841911052753433961397 11518766429161195634433881)
              ·
                refine ⟨8639074821870896725825411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11518766429161195634433881 8639074821870896725825411)
                ·
                  refine ⟨12958612232806345088738117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8639074821870896725825411 12958612232806345088738117)
                  ·
                    refine ⟨2429739793651189704138397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12958612232806345088738117 2429739793651189704138397)
                    ·
                      refine ⟨911152422619196139051899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2429739793651189704138397 911152422619196139051899)
                      ·
                        rfl

theorem cell23_1774463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 4, 3].length) (baseStart_1774463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1774463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1774463 prefixEnd_1774463 := by exact prefixLift 1774463
  have htrace : WordTrace (prefixWord ++ tailWord_1774463) baseStart_1774463 baseEnd_1774463 := by
    simpa [prefixWord, tailWord_1774463, baseEnd_1774463] using wordTrace_append hprefix tailTrace_1774463
  have hstable : (prefixWord ++ tailWord_1774463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774463).length < 2 ^ (prefixWord ++ tailWord_1774463).sum := by decide
  have hdescent : baseEnd_1774463 < baseStart_1774463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774497 : List Nat := [1, 2, 3, 4, 1, 2, 1, 2, 2, 2, 3]
def baseStart_1774497 : Nat := 118140960795 + 1774497 * 2 ^ 59
def prefixEnd_1774497 : Nat := 4983230072969 + 3 ^ 40 * 1774497 * 2
def baseEnd_1774497 : Nat := 911169880961449006026743

theorem tailTrace_1774497 : CollatzResearch.WordTrace tailWord_1774497 prefixEnd_1774497 911169880961449006026743 := by
  unfold tailWord_1774497
  simp only [CollatzResearch.WordTrace]
  refine ⟨64721222652307903804873745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43147481768205269203249163 64721222652307903804873745)
  ·
    refine ⟨48540916989230927853655309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64721222652307903804873745 48540916989230927853655309)
    ·
      refine ⟨18202843870961597945120741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48540916989230927853655309 18202843870961597945120741)
      ·
        refine ⟨3413033225805299614710139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18202843870961597945120741 3413033225805299614710139)
        ·
          refine ⟨5119549838707949422065209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3413033225805299614710139 5119549838707949422065209)
          ·
            refine ⟨3839662379030962066548907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5119549838707949422065209 3839662379030962066548907)
            ·
              refine ⟨5759493568546443099823361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3839662379030962066548907 5759493568546443099823361)
              ·
                refine ⟨4319620176409832324867521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5759493568546443099823361 4319620176409832324867521)
                ·
                  refine ⟨3239715132307374243650641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4319620176409832324867521 3239715132307374243650641)
                  ·
                    refine ⟨2429786349230530682737981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3239715132307374243650641 2429786349230530682737981)
                    ·
                      refine ⟨911169880961449006026743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2429786349230530682737981 911169880961449006026743)
                      ·
                        rfl

theorem cell23_1774497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_1774497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1774497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1774497 prefixEnd_1774497 := by exact prefixLift 1774497
  have htrace : WordTrace (prefixWord ++ tailWord_1774497) baseStart_1774497 baseEnd_1774497 := by
    simpa [prefixWord, tailWord_1774497, baseEnd_1774497] using wordTrace_append hprefix tailTrace_1774497
  have hstable : (prefixWord ++ tailWord_1774497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774497).length < 2 ^ (prefixWord ++ tailWord_1774497).sum := by decide
  have hdescent : baseEnd_1774497 < baseStart_1774497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774543 : List Nat := [1, 1, 2, 1, 1, 6, 1, 1, 3, 6]
def baseStart_1774543 : Nat := 118140960795 + 1774543 * 2 ^ 59
def prefixEnd_1774543 : Nat := 4983230072969 + 3 ^ 40 * 1774543 * 2
def baseEnd_1774543 : Nat := 303731167023851942017177

theorem tailTrace_1774543 : CollatzResearch.WordTrace tailWord_1774543 prefixEnd_1774543 303731167023851942017177 := by
  unfold tailWord_1774543
  simp only [CollatzResearch.WordTrace]
  refine ⟨64722900410141253661048283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43148600273427502440698855 64722900410141253661048283)
  ·
    refine ⟨97084350615211880491572425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64722900410141253661048283 97084350615211880491572425)
    ·
      refine ⟨72813262961408910368679319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97084350615211880491572425 72813262961408910368679319)
      ·
        refine ⟨109219894442113365553018979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72813262961408910368679319 109219894442113365553018979)
        ·
          refine ⟨163829841663170048329528469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109219894442113365553018979 163829841663170048329528469)
          ·
            refine ⟨7679523827961096015446647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 163829841663170048329528469 7679523827961096015446647)
            ·
              refine ⟨11519285741941644023169971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7679523827961096015446647 11519285741941644023169971)
              ·
                refine ⟨17278928612912466034754957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11519285741941644023169971 17278928612912466034754957)
                ·
                  refine ⟨6479598229842174763033109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17278928612912466034754957 6479598229842174763033109)
                  ·
                    refine ⟨303731167023851942017177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6479598229842174763033109 303731167023851942017177)
                    ·
                      rfl

theorem cell23_1774543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3, 6].length) (baseStart_1774543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1774543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1774543 prefixEnd_1774543 := by exact prefixLift 1774543
  have htrace : WordTrace (prefixWord ++ tailWord_1774543) baseStart_1774543 baseEnd_1774543 := by
    simpa [prefixWord, tailWord_1774543, baseEnd_1774543] using wordTrace_append hprefix tailTrace_1774543
  have hstable : (prefixWord ++ tailWord_1774543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774543).length < 2 ^ (prefixWord ++ tailWord_1774543).sum := by decide
  have hdescent : baseEnd_1774543 < baseStart_1774543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774577 : List Nat := [1, 2, 2, 2, 4, 1, 2, 3, 2, 4]
def baseStart_1774577 : Nat := 118140960795 + 1774577 * 2 ^ 59
def prefixEnd_1774577 : Nat := 4983230072969 + 3 ^ 40 * 1774577 * 2
def baseEnd_1774577 : Nat := 303736986471269564342125

theorem tailTrace_1774577 : CollatzResearch.WordTrace tailWord_1774577 prefixEnd_1774577 303736986471269564342125 := by
  unfold tailWord_1774577
  simp only [CollatzResearch.WordTrace]
  refine ⟨64724140492018077467785985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43149426994678718311857323 64724140492018077467785985)
  ·
    refine ⟨48543105369013558100839489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64724140492018077467785985 48543105369013558100839489)
    ·
      refine ⟨36407329026760168575629617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48543105369013558100839489 36407329026760168575629617)
      ·
        refine ⟨27305496770070126431722213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36407329026760168575629617 27305496770070126431722213)
        ·
          refine ⟨5119780644388148705947915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27305496770070126431722213 5119780644388148705947915)
          ·
            refine ⟨7679670966582223058921873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5119780644388148705947915 7679670966582223058921873)
            ·
              refine ⟨5759753224936667294191405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7679670966582223058921873 5759753224936667294191405)
              ·
                refine ⟨2159907459351250235321777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5759753224936667294191405 2159907459351250235321777)
                ·
                  refine ⟨1619930594513437676491333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2159907459351250235321777 1619930594513437676491333)
                  ·
                    refine ⟨303736986471269564342125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1619930594513437676491333 303736986471269564342125)
                    ·
                      rfl

theorem cell23_1774577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 3, 2, 4].length) (baseStart_1774577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1774577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1774577 prefixEnd_1774577 := by exact prefixLift 1774577
  have htrace : WordTrace (prefixWord ++ tailWord_1774577) baseStart_1774577 baseEnd_1774577 := by
    simpa [prefixWord, tailWord_1774577, baseEnd_1774577] using wordTrace_append hprefix tailTrace_1774577
  have hstable : (prefixWord ++ tailWord_1774577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774577).length < 2 ^ (prefixWord ++ tailWord_1774577).sum := by decide
  have hdescent : baseEnd_1774577 < baseStart_1774577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774604 : List Nat := [2, 2, 1, 2, 3, 2, 4, 1, 1, 2, 3]
def baseStart_1774604 : Nat := 118140960795 + 1774604 * 2 ^ 59
def prefixEnd_1774604 : Nat := 4983230072969 + 3 ^ 40 * 1774604 * 2
def baseEnd_1774604 : Nat := 911224823391480087388751

theorem tailTrace_1774604 : CollatzResearch.WordTrace tailWord_1774604 prefixEnd_1774604 911224823391480087388751 := by
  unfold tailWord_1774604
  simp only [CollatzResearch.WordTrace]
  refine ⟨32362562631460130539509433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43150083508613507386012577 32362562631460130539509433)
  ·
    refine ⟨24271921973595097904632075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32362562631460130539509433 24271921973595097904632075)
    ·
      refine ⟨36407882960392646856948113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24271921973595097904632075 36407882960392646856948113)
      ·
        refine ⟨27305912220294485142711085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36407882960392646856948113 27305912220294485142711085)
        ·
          refine ⟨10239717082610431928516657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27305912220294485142711085 10239717082610431928516657)
          ·
            refine ⟨7679787811957823946387493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10239717082610431928516657 7679787811957823946387493)
            ·
              refine ⟨1439960214742091989947655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7679787811957823946387493 1439960214742091989947655)
              ·
                refine ⟨2159940322113137984921483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1439960214742091989947655 2159940322113137984921483)
                ·
                  refine ⟨3239910483169706977382225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2159940322113137984921483 3239910483169706977382225)
                  ·
                    refine ⟨2429932862377280233036669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3239910483169706977382225 2429932862377280233036669)
                    ·
                      refine ⟨911224823391480087388751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2429932862377280233036669 911224823391480087388751)
                      ·
                        rfl

theorem cell23_1774604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 1, 1, 2, 3].length) (baseStart_1774604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1774604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1774604 prefixEnd_1774604 := by exact prefixLift 1774604
  have htrace : WordTrace (prefixWord ++ tailWord_1774604) baseStart_1774604 baseEnd_1774604 := by
    simpa [prefixWord, tailWord_1774604, baseEnd_1774604] using wordTrace_append hprefix tailTrace_1774604
  have hstable : (prefixWord ++ tailWord_1774604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774604).length < 2 ^ (prefixWord ++ tailWord_1774604).sum := by decide
  have hdescent : baseEnd_1774604 < baseStart_1774604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774685 : List Nat := [1, 4, 4, 1, 2, 2, 2, 1, 2, 1, 3]
def baseStart_1774685 : Nat := 118140960795 + 1774685 * 2 ^ 59
def prefixEnd_1774685 : Nat := 4983230072969 + 3 ^ 40 * 1774685 * 2
def baseEnd_1774685 : Nat := 911266415324494270475879

theorem tailTrace_1774685 : CollatzResearch.WordTrace tailWord_1774685 prefixEnd_1774685 911266415324494270475879 := by
  unfold tailWord_1774685
  simp only [CollatzResearch.WordTrace]
  refine ⟨64728079575626811912717509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43152053050417874608478339 64728079575626811912717509)
  ·
    refine ⟨12136514920430027233634533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64728079575626811912717509 12136514920430027233634533)
    ·
      refine ⟨2275596547580630106306475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12136514920430027233634533 2275596547580630106306475)
      ·
        refine ⟨3413394821370945159459713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2275596547580630106306475 3413394821370945159459713)
        ·
          refine ⟨2560046116028208869594785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3413394821370945159459713 2560046116028208869594785)
          ·
            refine ⟨1920034587021156652196089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2560046116028208869594785 1920034587021156652196089)
            ·
              refine ⟨1440025940265867489147067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1920034587021156652196089 1440025940265867489147067)
              ·
                refine ⟨2160038910398801233720601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1440025940265867489147067 2160038910398801233720601)
                ·
                  refine ⟨1620029182799100925290451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2160038910398801233720601 1620029182799100925290451)
                  ·
                    refine ⟨2430043774198651387935677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1620029182799100925290451 2430043774198651387935677)
                    ·
                      refine ⟨911266415324494270475879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2430043774198651387935677 911266415324494270475879)
                      ·
                        rfl

theorem cell23_1774685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_1774685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1774685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1774685 prefixEnd_1774685 := by exact prefixLift 1774685
  have htrace : WordTrace (prefixWord ++ tailWord_1774685) baseStart_1774685 baseEnd_1774685 := by
    simpa [prefixWord, tailWord_1774685, baseEnd_1774685] using wordTrace_append hprefix tailTrace_1774685
  have hstable : (prefixWord ++ tailWord_1774685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774685).length < 2 ^ (prefixWord ++ tailWord_1774685).sum := by decide
  have hdescent : baseEnd_1774685 < baseStart_1774685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774720 : List Nat := [2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 5]
def baseStart_1774720 : Nat := 118140960795 + 1774720 * 2 ^ 59
def prefixEnd_1774720 : Nat := 4983230072969 + 3 ^ 40 * 1774720 * 2
def baseEnd_1774720 : Nat := 911284387147401633538217

theorem tailTrace_1774720 : CollatzResearch.WordTrace tailWord_1774720 prefixEnd_1774720 911284387147401633538217 := by
  unfold tailWord_1774720
  simp only [CollatzResearch.WordTrace]
  refine ⟨32364678065250006445120807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43152904087000008593494409 32364678065250006445120807)
  ·
    refine ⟨48547017097875009667681211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32364678065250006445120807 48547017097875009667681211)
    ·
      refine ⟨72820525646812514501521817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48547017097875009667681211 72820525646812514501521817)
      ·
        refine ⟨54615394235109385876141363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72820525646812514501521817 54615394235109385876141363)
        ·
          refine ⟨81923091352664078814212045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54615394235109385876141363 81923091352664078814212045)
          ·
            refine ⟨30721159257249029555329517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81923091352664078814212045 30721159257249029555329517)
            ·
              refine ⟨11520434721468386083248569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30721159257249029555329517 11520434721468386083248569)
              ·
                refine ⟨8640326041101289562436427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11520434721468386083248569 8640326041101289562436427)
                ·
                  refine ⟨12960489061651934343654641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8640326041101289562436427 12960489061651934343654641)
                  ·
                    refine ⟨9720366796238950757740981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12960489061651934343654641 9720366796238950757740981)
                    ·
                      refine ⟨911284387147401633538217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9720366796238950757740981 911284387147401633538217)
                      ·
                        rfl

theorem cell23_1774720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 5].length) (baseStart_1774720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1774720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1774720 prefixEnd_1774720 := by exact prefixLift 1774720
  have htrace : WordTrace (prefixWord ++ tailWord_1774720) baseStart_1774720 baseEnd_1774720 := by
    simpa [prefixWord, tailWord_1774720, baseEnd_1774720] using wordTrace_append hprefix tailTrace_1774720
  have hstable : (prefixWord ++ tailWord_1774720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774720).length < 2 ^ (prefixWord ++ tailWord_1774720).sum := by decide
  have hdescent : baseEnd_1774720 < baseStart_1774720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774734 : List Nat := [4, 1, 1, 3, 2, 1, 1, 1, 2, 5, 2]
def baseStart_1774734 : Nat := 118140960795 + 1774734 * 2 ^ 59
def prefixEnd_1774734 : Nat := 4983230072969 + 3 ^ 40 * 1774734 * 2
def baseEnd_1774734 : Nat := 911291575876564578763153

theorem tailTrace_1774734 : CollatzResearch.WordTrace tailWord_1774734 prefixEnd_1774734 911291575876564578763153 := by
  unfold tailWord_1774734
  simp only [CollatzResearch.WordTrace]
  refine ⟨8091233344056161660156407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43153244501632862187500837 8091233344056161660156407)
  ·
    refine ⟨12136850016084242490234611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8091233344056161660156407 12136850016084242490234611)
    ·
      refine ⟨18205275024126363735351917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12136850016084242490234611 18205275024126363735351917)
      ·
        refine ⟨6826978134047386400756969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18205275024126363735351917 6826978134047386400756969)
        ·
          refine ⟨5120233600535539800567727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6826978134047386400756969 5120233600535539800567727)
          ·
            refine ⟨7680350400803309700851591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5120233600535539800567727 7680350400803309700851591)
            ·
              refine ⟨11520525601204964551277387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7680350400803309700851591 11520525601204964551277387)
              ·
                refine ⟨17280788401807446826916081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11520525601204964551277387 17280788401807446826916081)
                ·
                  refine ⟨12960591301355585120187061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17280788401807446826916081 12960591301355585120187061)
                  ·
                    refine ⟨1215055434502086105017537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12960591301355585120187061 1215055434502086105017537)
                    ·
                      refine ⟨911291575876564578763153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1215055434502086105017537 911291575876564578763153)
                      ·
                        rfl

theorem cell23_1774734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_1774734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1774734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1774734 prefixEnd_1774734 := by exact prefixLift 1774734
  have htrace : WordTrace (prefixWord ++ tailWord_1774734) baseStart_1774734 baseEnd_1774734 := by
    simpa [prefixWord, tailWord_1774734, baseEnd_1774734] using wordTrace_append hprefix tailTrace_1774734
  have hstable : (prefixWord ++ tailWord_1774734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774734).length < 2 ^ (prefixWord ++ tailWord_1774734).sum := by decide
  have hdescent : baseEnd_1774734 < baseStart_1774734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774757 : List Nat := [1, 3, 1, 2, 1, 4, 1, 1, 5, 4]
def baseStart_1774757 : Nat := 118140960795 + 1774757 * 2 ^ 59
def prefixEnd_1774757 : Nat := 4983230072969 + 3 ^ 40 * 1774757 * 2
def baseEnd_1774757 : Nat := 303767795310539329591849

theorem tailTrace_1774757 : CollatzResearch.WordTrace tailWord_1774757 prefixEnd_1774757 303767795310539329591849 := by
  unfold tailWord_1774757
  simp only [CollatzResearch.WordTrace]
  refine ⟨64730705631365968209338525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43153803754243978806225683 64730705631365968209338525)
  ·
    refine ⟨24274014611762238078501947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64730705631365968209338525 24274014611762238078501947)
    ·
      refine ⟨36411021917643357117752921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24274014611762238078501947 36411021917643357117752921)
      ·
        refine ⟨27308266438232517838314691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36411021917643357117752921 27308266438232517838314691)
        ·
          refine ⟨40962399657348776757472037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27308266438232517838314691 40962399657348776757472037)
          ·
            refine ⟨7680449935752895642026007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40962399657348776757472037 7680449935752895642026007)
            ·
              refine ⟨11520674903629343463039011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7680449935752895642026007 11520674903629343463039011)
              ·
                refine ⟨17281012355444015194558517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11520674903629343463039011 17281012355444015194558517)
                ·
                  refine ⟨1620094908322876424489861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17281012355444015194558517 1620094908322876424489861)
                  ·
                    refine ⟨303767795310539329591849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1620094908322876424489861 303767795310539329591849)
                    ·
                      rfl

theorem cell23_1774757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 5, 4].length) (baseStart_1774757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1774757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1774757 prefixEnd_1774757 := by exact prefixLift 1774757
  have htrace : WordTrace (prefixWord ++ tailWord_1774757) baseStart_1774757 baseEnd_1774757 := by
    simpa [prefixWord, tailWord_1774757, baseEnd_1774757] using wordTrace_append hprefix tailTrace_1774757
  have hstable : (prefixWord ++ tailWord_1774757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774757).length < 2 ^ (prefixWord ++ tailWord_1774757).sum := by decide
  have hdescent : baseEnd_1774757 < baseStart_1774757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774824 : List Nat := [2, 1, 4, 1, 2, 1, 1, 3, 1, 5, 2]
def baseStart_1774824 : Nat := 118140960795 + 1774824 * 2 ^ 59
def prefixEnd_1774824 : Nat := 4983230072969 + 3 ^ 40 * 1774824 * 2
def baseEnd_1774824 : Nat := 911337789135469226637739

theorem tailTrace_1774824 : CollatzResearch.WordTrace tailWord_1774824 prefixEnd_1774824 911337789135469226637739 := by
  unfold tailWord_1774824
  simp only [CollatzResearch.WordTrace]
  refine ⟨32366574661061619326013763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43155432881415492434685017 32366574661061619326013763)
  ·
    refine ⟨48549861991592428989020645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32366574661061619326013763 48549861991592428989020645)
    ·
      refine ⟨9103099123423580435441371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48549861991592428989020645 9103099123423580435441371)
      ·
        refine ⟨13654648685135370653162057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9103099123423580435441371 13654648685135370653162057)
        ·
          refine ⟨10240986513851527989871543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13654648685135370653162057 10240986513851527989871543)
          ·
            refine ⟨15361479770777291984807315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10240986513851527989871543 15361479770777291984807315)
            ·
              refine ⟨23042219656165937977210973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15361479770777291984807315 23042219656165937977210973)
              ·
                refine ⟨8640832371062226741454115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23042219656165937977210973 8640832371062226741454115)
                ·
                  refine ⟨12961248556593340112181173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8640832371062226741454115 12961248556593340112181173)
                  ·
                    refine ⟨1215117052180625635516985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12961248556593340112181173 1215117052180625635516985)
                    ·
                      refine ⟨911337789135469226637739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1215117052180625635516985 911337789135469226637739)
                      ·
                        rfl

theorem cell23_1774824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 1, 5, 2].length) (baseStart_1774824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1774824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1774824 prefixEnd_1774824 := by exact prefixLift 1774824
  have htrace : WordTrace (prefixWord ++ tailWord_1774824) baseStart_1774824 baseEnd_1774824 := by
    simpa [prefixWord, tailWord_1774824, baseEnd_1774824] using wordTrace_append hprefix tailTrace_1774824
  have hstable : (prefixWord ++ tailWord_1774824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774824).length < 2 ^ (prefixWord ++ tailWord_1774824).sum := by decide
  have hdescent : baseEnd_1774824 < baseStart_1774824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774857 : List Nat := [1, 2, 1, 1, 3, 3, 1, 4, 1, 1, 5]
def baseStart_1774857 : Nat := 118140960795 + 1774857 * 2 ^ 59
def prefixEnd_1774857 : Nat := 4983230072969 + 3 ^ 40 * 1774857 * 2
def baseEnd_1774857 : Nat := 911354733997067597525087

theorem tailTrace_1774857 : CollatzResearch.WordTrace tailWord_1774857 prefixEnd_1774857 911354733997067597525087 := by
  unfold tailWord_1774857
  simp only [CollatzResearch.WordTrace]
  refine ⟨64734352931003685287978825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43156235287335790191985883 64734352931003685287978825)
  ·
    refine ⟨48550764698252763965984119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64734352931003685287978825 48550764698252763965984119)
    ·
      refine ⟨72826147047379145948976179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48550764698252763965984119 72826147047379145948976179)
      ·
        refine ⟨109239220571068718923464269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72826147047379145948976179 109239220571068718923464269)
        ·
          refine ⟨40964707714150769596299101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109239220571068718923464269 40964707714150769596299101)
          ·
            refine ⟨15361765392806538598612163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40964707714150769596299101 15361765392806538598612163)
            ·
              refine ⟨23042648089209807897918245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15361765392806538598612163 23042648089209807897918245)
              ·
                refine ⟨4320496516726838980859671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23042648089209807897918245 4320496516726838980859671)
                ·
                  refine ⟨6480744775090258471289507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4320496516726838980859671 6480744775090258471289507)
                  ·
                    refine ⟨9721117162635387706934261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6480744775090258471289507 9721117162635387706934261)
                    ·
                      refine ⟨911354733997067597525087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9721117162635387706934261 911354733997067597525087)
                      ·
                        rfl

theorem cell23_1774857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4, 1, 1, 5].length) (baseStart_1774857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1774857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1774857 prefixEnd_1774857 := by exact prefixLift 1774857
  have htrace : WordTrace (prefixWord ++ tailWord_1774857) baseStart_1774857 baseEnd_1774857 := by
    simpa [prefixWord, tailWord_1774857, baseEnd_1774857] using wordTrace_append hprefix tailTrace_1774857
  have hstable : (prefixWord ++ tailWord_1774857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774857).length < 2 ^ (prefixWord ++ tailWord_1774857).sum := by decide
  have hdescent : baseEnd_1774857 < baseStart_1774857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774871 : List Nat := [1, 1, 3, 4, 1, 1, 2, 1, 5, 2, 2]
def baseStart_1774871 : Nat := 118140960795 + 1774871 * 2 ^ 59
def prefixEnd_1774871 : Nat := 4983230072969 + 3 ^ 40 * 1774871 * 2
def baseEnd_1774871 : Nat := 911361922726230542750023

theorem tailTrace_1774871 : CollatzResearch.WordTrace tailWord_1774871 prefixEnd_1774871 911361922726230542750023 := by
  unfold tailWord_1774871
  simp only [CollatzResearch.WordTrace]
  refine ⟨64734863552952965678988467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43156575701968643785992311 64734863552952965678988467)
  ·
    refine ⟨97102295329429448518482701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64734863552952965678988467 97102295329429448518482701)
    ·
      refine ⟨36413360748536043194431013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97102295329429448518482701 36413360748536043194431013)
      ·
        refine ⟨6827505140350508098955815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36413360748536043194431013 6827505140350508098955815)
        ·
          refine ⟨10241257710525762148433723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6827505140350508098955815 10241257710525762148433723)
          ·
            refine ⟨15361886565788643222650585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10241257710525762148433723 15361886565788643222650585)
            ·
              refine ⟨11521414924341482416987939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15361886565788643222650585 11521414924341482416987939)
              ·
                refine ⟨17282122386512223625481909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11521414924341482416987939 17282122386512223625481909)
                ·
                  refine ⟨1620198973735520964888929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17282122386512223625481909 1620198973735520964888929)
                  ·
                    refine ⟨1215149230301640723666697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1620198973735520964888929 1215149230301640723666697)
                    ·
                      refine ⟨911361922726230542750023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1215149230301640723666697 911361922726230542750023)
                      ·
                        rfl

theorem cell23_1774871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_1774871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1774871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1774871 prefixEnd_1774871 := by exact prefixLift 1774871
  have htrace : WordTrace (prefixWord ++ tailWord_1774871) baseStart_1774871 baseEnd_1774871 := by
    simpa [prefixWord, tailWord_1774871, baseEnd_1774871] using wordTrace_append hprefix tailTrace_1774871
  have hstable : (prefixWord ++ tailWord_1774871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774871).length < 2 ^ (prefixWord ++ tailWord_1774871).sum := by decide
  have hdescent : baseEnd_1774871 < baseStart_1774871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774884 : List Nat := [2, 3, 1, 3, 1, 1, 3, 2, 1, 2, 4]
def baseStart_1774884 : Nat := 118140960795 + 1774884 * 2 ^ 59
def prefixEnd_1774884 : Nat := 4983230072969 + 3 ^ 40 * 1774884 * 2
def baseEnd_1774884 : Nat := 911368597974738991887463

theorem tailTrace_1774884 : CollatzResearch.WordTrace tailWord_1774884 prefixEnd_1774884 911368597974738991887463 := by
  unfold tailWord_1774884
  simp only [CollatzResearch.WordTrace]
  refine ⟨32367668850952934449605853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43156891801270579266141137 32367668850952934449605853)
  ·
    refine ⟨12137875819107350418602195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32367668850952934449605853 12137875819107350418602195)
    ·
      refine ⟨18206813728661025627903293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12137875819107350418602195 18206813728661025627903293)
      ·
        refine ⟨6827555148247884610463735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18206813728661025627903293 6827555148247884610463735)
        ·
          refine ⟨10241332722371826915695603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6827555148247884610463735 10241332722371826915695603)
          ·
            refine ⟨15361999083557740373543405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10241332722371826915695603 15361999083557740373543405)
            ·
              refine ⟨5760749656334152640078777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15361999083557740373543405 5760749656334152640078777)
              ·
                refine ⟨4320562242250614480059083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5760749656334152640078777 4320562242250614480059083)
                ·
                  refine ⟨6480843363375921720088625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4320562242250614480059083 6480843363375921720088625)
                  ·
                    refine ⟨4860632522531941290066469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6480843363375921720088625 4860632522531941290066469)
                    ·
                      refine ⟨911368597974738991887463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4860632522531941290066469 911368597974738991887463)
                      ·
                        rfl

theorem cell23_1774884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_1774884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1774884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1774884 prefixEnd_1774884 := by exact prefixLift 1774884
  have htrace : WordTrace (prefixWord ++ tailWord_1774884) baseStart_1774884 baseEnd_1774884 := by
    simpa [prefixWord, tailWord_1774884, baseEnd_1774884] using wordTrace_append hprefix tailTrace_1774884
  have hstable : (prefixWord ++ tailWord_1774884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774884).length < 2 ^ (prefixWord ++ tailWord_1774884).sum := by decide
  have hdescent : baseEnd_1774884 < baseStart_1774884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774888 : List Nat := [2, 1, 5, 1, 2, 2, 3, 1, 1, 1, 4]
def baseStart_1774888 : Nat := 118140960795 + 1774888 * 2 ^ 59
def prefixEnd_1774888 : Nat := 4983230072969 + 3 ^ 40 * 1774888 * 2
def baseEnd_1774888 : Nat := 911370651897356976237445

theorem tailTrace_1774888 : CollatzResearch.WordTrace tailWord_1774888 prefixEnd_1774888 911370651897356976237445 := by
  unfold tailWord_1774888
  simp only [CollatzResearch.WordTrace]
  refine ⟨32367741796945688791178659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43156989062594251721571545 32367741796945688791178659)
  ·
    refine ⟨48551612695418533186767989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32367741796945688791178659 48551612695418533186767989)
    ·
      refine ⟨4551713690195487486259499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48551612695418533186767989 4551713690195487486259499)
      ·
        refine ⟨6827570535293231229389249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4551713690195487486259499 6827570535293231229389249)
        ·
          refine ⟨5120677901469923422041937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6827570535293231229389249 5120677901469923422041937)
          ·
            refine ⟨3840508426102442566531453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5120677901469923422041937 3840508426102442566531453)
            ·
              refine ⟨1440190659788415962449295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3840508426102442566531453 1440190659788415962449295)
              ·
                refine ⟨2160285989682623943673943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1440190659788415962449295 2160285989682623943673943)
                ·
                  refine ⟨3240428984523935915510915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2160285989682623943673943 3240428984523935915510915)
                  ·
                    refine ⟨4860643476785903873266373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3240428984523935915510915 4860643476785903873266373)
                    ·
                      refine ⟨911370651897356976237445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4860643476785903873266373 911370651897356976237445)
                      ·
                        rfl

theorem cell23_1774888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_1774888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1774888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1774888 prefixEnd_1774888 := by exact prefixLift 1774888
  have htrace : WordTrace (prefixWord ++ tailWord_1774888) baseStart_1774888 baseEnd_1774888 := by
    simpa [prefixWord, tailWord_1774888, baseEnd_1774888] using wordTrace_append hprefix tailTrace_1774888
  have hstable : (prefixWord ++ tailWord_1774888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774888).length < 2 ^ (prefixWord ++ tailWord_1774888).sum := by decide
  have hdescent : baseEnd_1774888 < baseStart_1774888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774921 : List Nat := [1, 2, 1, 1, 2, 3, 4, 3, 2, 1, 3]
def baseStart_1774921 : Nat := 118140960795 + 1774921 * 2 ^ 59
def prefixEnd_1774921 : Nat := 4983230072969 + 3 ^ 40 * 1774921 * 2
def baseEnd_1774921 : Nat := 911387596758955347124793

theorem tailTrace_1774921 : CollatzResearch.WordTrace tailWord_1774921 prefixEnd_1774921 911387596758955347124793 := by
  unfold tailWord_1774921
  simp only [CollatzResearch.WordTrace]
  refine ⟨64736687202771824218308617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43157791468514549478872411 64736687202771824218308617)
  ·
    refine ⟨48552515402078868163731463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64736687202771824218308617 48552515402078868163731463)
    ·
      refine ⟨72828773103118302245597195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48552515402078868163731463 72828773103118302245597195)
      ·
        refine ⟨109243159654677453368395793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72828773103118302245597195 109243159654677453368395793)
        ·
          refine ⟨81932369741008090026296845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109243159654677453368395793 81932369741008090026296845)
          ·
            refine ⟨30724638652878033759861317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81932369741008090026296845 30724638652878033759861317)
            ·
              refine ⟨5760869747414631329973997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30724638652878033759861317 5760869747414631329973997)
              ·
                refine ⟨2160326155280486748740249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5760869747414631329973997 2160326155280486748740249)
                ·
                  refine ⟨1620244616460365061555187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2160326155280486748740249 1620244616460365061555187)
                  ·
                    refine ⟨2430366924690547592332781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1620244616460365061555187 2430366924690547592332781)
                    ·
                      refine ⟨911387596758955347124793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2430366924690547592332781 911387596758955347124793)
                      ·
                        rfl

theorem cell23_1774921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 3, 2, 1, 3].length) (baseStart_1774921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1774921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1774921 prefixEnd_1774921 := by exact prefixLift 1774921
  have htrace : WordTrace (prefixWord ++ tailWord_1774921) baseStart_1774921 baseEnd_1774921 := by
    simpa [prefixWord, tailWord_1774921, baseEnd_1774921] using wordTrace_append hprefix tailTrace_1774921
  have hstable : (prefixWord ++ tailWord_1774921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774921).length < 2 ^ (prefixWord ++ tailWord_1774921).sum := by decide
  have hdescent : baseEnd_1774921 < baseStart_1774921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774931 : List Nat := [1, 1, 1, 2, 1, 1, 6, 4, 1, 3, 2]
def baseStart_1774931 : Nat := 118140960795 + 1774931 * 2 ^ 59
def prefixEnd_1774931 : Nat := 4983230072969 + 3 ^ 40 * 1774931 * 2
def baseEnd_1774931 : Nat := 911392731565500307999747

theorem tailTrace_1774931 : CollatzResearch.WordTrace tailWord_1774931 prefixEnd_1774931 911392731565500307999747 := by
  unfold tailWord_1774931
  simp only [CollatzResearch.WordTrace]
  refine ⟨64737051932735595926172647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43158034621823730617448431 64737051932735595926172647)
  ·
    refine ⟨97105577899103393889258971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64737051932735595926172647 97105577899103393889258971)
    ·
      refine ⟨145658366848655090833888457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97105577899103393889258971 145658366848655090833888457)
      ·
        refine ⟨109243775136491318125416343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145658366848655090833888457 109243775136491318125416343)
        ·
          refine ⟨163865662704736977188124515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109243775136491318125416343 163865662704736977188124515)
          ·
            refine ⟨245798494057105465782186773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163865662704736977188124515 245798494057105465782186773)
            ·
              refine ⟨11521804408926818708540005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 245798494057105465782186773 11521804408926818708540005)
              ·
                refine ⟨2160338326673778507851251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11521804408926818708540005 2160338326673778507851251)
                ·
                  refine ⟨3240507490010667761776877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2160338326673778507851251 3240507490010667761776877)
                  ·
                    refine ⟨1215190308754000410666329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3240507490010667761776877 1215190308754000410666329)
                    ·
                      refine ⟨911392731565500307999747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1215190308754000410666329 911392731565500307999747)
                      ·
                        rfl

theorem cell23_1774931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 4, 1, 3, 2].length) (baseStart_1774931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1774931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1774931 prefixEnd_1774931 := by exact prefixLift 1774931
  have htrace : WordTrace (prefixWord ++ tailWord_1774931) baseStart_1774931 baseEnd_1774931 := by
    simpa [prefixWord, tailWord_1774931, baseEnd_1774931] using wordTrace_append hprefix tailTrace_1774931
  have hstable : (prefixWord ++ tailWord_1774931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774931).length < 2 ^ (prefixWord ++ tailWord_1774931).sum := by decide
  have hdescent : baseEnd_1774931 < baseStart_1774931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774948 : List Nat := [2, 3, 1, 1, 3, 3, 1, 3, 1, 3, 2]
def baseStart_1774948 : Nat := 118140960795 + 1774948 * 2 ^ 59
def prefixEnd_1774948 : Nat := 4983230072969 + 3 ^ 40 * 1774948 * 2
def baseEnd_1774948 : Nat := 911401460736626741487169

theorem tailTrace_1774948 : CollatzResearch.WordTrace tailWord_1774948 prefixEnd_1774948 911401460736626741487169 := by
  unfold tailWord_1774948
  simp only [CollatzResearch.WordTrace]
  refine ⟨32368835986837003914770749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43158447982449338553027665 32368835986837003914770749)
  ·
    refine ⟨12138313495063876468039031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32368835986837003914770749 12138313495063876468039031)
    ·
      refine ⟨18207470242595814702058547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12138313495063876468039031 18207470242595814702058547)
      ·
        refine ⟨27311205363893722053087821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18207470242595814702058547 27311205363893722053087821)
        ·
          refine ⟨10241702011460145769907933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27311205363893722053087821 10241702011460145769907933)
          ·
            refine ⟨3840638254297554663715475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10241702011460145769907933 3840638254297554663715475)
            ·
              refine ⟨5760957381446331995573213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3840638254297554663715475 5760957381446331995573213)
              ·
                refine ⟨2160359018042374498339955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5760957381446331995573213 2160359018042374498339955)
                ·
                  refine ⟨3240538527063561747509933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2160359018042374498339955 3240538527063561747509933)
                  ·
                    refine ⟨1215201947648835655316225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3240538527063561747509933 1215201947648835655316225)
                    ·
                      refine ⟨911401460736626741487169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1215201947648835655316225 911401460736626741487169)
                      ·
                        rfl

theorem cell23_1774948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 3, 1, 3, 2].length) (baseStart_1774948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1774948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1774948 prefixEnd_1774948 := by exact prefixLift 1774948
  have htrace : WordTrace (prefixWord ++ tailWord_1774948) baseStart_1774948 baseEnd_1774948 := by
    simpa [prefixWord, tailWord_1774948, baseEnd_1774948] using wordTrace_append hprefix tailTrace_1774948
  have hstable : (prefixWord ++ tailWord_1774948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774948).length < 2 ^ (prefixWord ++ tailWord_1774948).sum := by decide
  have hdescent : baseEnd_1774948 < baseStart_1774948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1774984 : List Nat := [2, 1, 3, 3, 1, 2, 2, 2, 7]
def baseStart_1774984 : Nat := 118140960795 + 1774984 * 2 ^ 59
def prefixEnd_1774984 : Nat := 4983230072969 + 3 ^ 40 * 1774984 * 2
def baseEnd_1774984 : Nat := 101268882893354288959667

theorem tailTrace_1774984 : CollatzResearch.WordTrace tailWord_1774984 prefixEnd_1774984 101268882893354288959667 := by
  unfold tailWord_1774984
  simp only [CollatzResearch.WordTrace]
  refine ⟨32369492500771792988926003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43159323334362390651901337 32369492500771792988926003)
  ·
    refine ⟨48554238751157689483389005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32369492500771792988926003 48554238751157689483389005)
    ·
      refine ⟨18207839531684133556270877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48554238751157689483389005 18207839531684133556270877)
      ·
        refine ⟨6827939824381550083601579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18207839531684133556270877 6827939824381550083601579)
        ·
          refine ⟨10241909736572325125402369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6827939824381550083601579 10241909736572325125402369)
          ·
            refine ⟨7681432302429243844051777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10241909736572325125402369 7681432302429243844051777)
            ·
              refine ⟨5761074226821932883038833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7681432302429243844051777 5761074226821932883038833)
              ·
                refine ⟨4320805670116449662279125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5761074226821932883038833 4320805670116449662279125)
                ·
                  refine ⟨101268882893354288959667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4320805670116449662279125 101268882893354288959667)
                  ·
                    rfl

theorem cell23_1774984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2, 7].length) (baseStart_1774984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1774984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1774984 prefixEnd_1774984 := by exact prefixLift 1774984
  have htrace : WordTrace (prefixWord ++ tailWord_1774984) baseStart_1774984 baseEnd_1774984 := by
    simpa [prefixWord, tailWord_1774984, baseEnd_1774984] using wordTrace_append hprefix tailTrace_1774984
  have hstable : (prefixWord ++ tailWord_1774984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1774984).length < 2 ^ (prefixWord ++ tailWord_1774984).sum := by decide
  have hdescent : baseEnd_1774984 < baseStart_1774984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1774984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775001 : List Nat := [1, 2, 1, 2, 1, 5, 3, 3, 5]
def baseStart_1775001 : Nat := 118140960795 + 1775001 * 2 ^ 59
def prefixEnd_1775001 : Nat := 4983230072969 + 3 ^ 40 * 1775001 * 2
def baseEnd_1775001 : Nat := 101269852801257226013825

theorem tailTrace_1775001 : CollatzResearch.WordTrace tailWord_1775001 prefixEnd_1775001 101269852801257226013825 := by
  unfold tailWord_1775001
  simp only [CollatzResearch.WordTrace]
  refine ⟨64739605042481997881220857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43159736694987998587480571 64739605042481997881220857)
  ·
    refine ⟨48554703781861498410915643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64739605042481997881220857 48554703781861498410915643)
    ·
      refine ⟨72832055672792247616373465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48554703781861498410915643 72832055672792247616373465)
      ·
        refine ⟨54624041754594185712280099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72832055672792247616373465 54624041754594185712280099)
        ·
          refine ⟨81936062631891278568420149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54624041754594185712280099 81936062631891278568420149)
          ·
            refine ⟨7681505871739807365789389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81936062631891278568420149 7681505871739807365789389)
            ·
              refine ⟨2880564701902427762171021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7681505871739807365789389 2880564701902427762171021)
              ·
                refine ⟨1080211763213410410814133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2880564701902427762171021 1080211763213410410814133)
                ·
                  refine ⟨101269852801257226013825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1080211763213410410814133 101269852801257226013825)
                  ·
                    rfl

theorem cell23_1775001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 3, 5].length) (baseStart_1775001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1775001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1775001 prefixEnd_1775001 := by exact prefixLift 1775001
  have htrace : WordTrace (prefixWord ++ tailWord_1775001) baseStart_1775001 baseEnd_1775001 := by
    simpa [prefixWord, tailWord_1775001, baseEnd_1775001] using wordTrace_append hprefix tailTrace_1775001
  have hstable : (prefixWord ++ tailWord_1775001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775001).length < 2 ^ (prefixWord ++ tailWord_1775001).sum := by decide
  have hdescent : baseEnd_1775001 < baseStart_1775001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775017 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 2, 2, 8]
def baseStart_1775017 : Nat := 118140960795 + 1775017 * 2 ^ 59
def prefixEnd_1775017 : Nat := 4983230072969 + 3 ^ 40 * 1775017 * 2
def baseEnd_1775017 : Nat := 911436890901786971524351

theorem tailTrace_1775017 : CollatzResearch.WordTrace tailWord_1775017 prefixEnd_1775017 911436890901786971524351 := by
  unfold tailWord_1775017
  simp only [CollatzResearch.WordTrace]
  refine ⟨64740188610424032613803305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43160125740282688409202203 64740188610424032613803305)
  ·
    refine ⟨48555141457818024460352479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64740188610424032613803305 48555141457818024460352479)
    ·
      refine ⟨72832712186727036690528719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48555141457818024460352479 72832712186727036690528719)
      ·
        refine ⟨109249068280090555035793079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72832712186727036690528719 109249068280090555035793079)
        ·
          refine ⟨163873602420135832553689619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109249068280090555035793079 163873602420135832553689619)
          ·
            refine ⟨245810403630203748830534429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163873602420135832553689619 245810403630203748830534429)
            ·
              refine ⟨92178901361326405811450411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 245810403630203748830534429 92178901361326405811450411)
              ·
                refine ⟨138268352041989608717175617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92178901361326405811450411 138268352041989608717175617)
                ·
                  refine ⟨103701264031492206537881713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138268352041989608717175617 103701264031492206537881713)
                  ·
                    refine ⟨77775948023619154903411285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 103701264031492206537881713 77775948023619154903411285)
                    ·
                      refine ⟨911436890901786971524351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 77775948023619154903411285 911436890901786971524351)
                      ·
                        rfl

theorem cell23_1775017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 2, 8].length) (baseStart_1775017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1775017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1775017 prefixEnd_1775017 := by exact prefixLift 1775017
  have htrace : WordTrace (prefixWord ++ tailWord_1775017) baseStart_1775017 baseEnd_1775017 := by
    simpa [prefixWord, tailWord_1775017, baseEnd_1775017] using wordTrace_append hprefix tailTrace_1775017
  have hstable : (prefixWord ++ tailWord_1775017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775017).length < 2 ^ (prefixWord ++ tailWord_1775017).sum := by decide
  have hdescent : baseEnd_1775017 < baseStart_1775017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775071 : List Nat := [1, 1, 2, 3, 3, 1, 1, 4, 2, 2, 3]
def baseStart_1775071 : Nat := 118140960795 + 1775071 * 2 ^ 59
def prefixEnd_1775071 : Nat := 4983230072969 + 3 ^ 40 * 1775071 * 2
def baseEnd_1775071 : Nat := 911464618857129760249103

theorem tailTrace_1775071 : CollatzResearch.WordTrace tailWord_1775071 prefixEnd_1775071 911464618857129760249103 := by
  unfold tailWord_1775071
  simp only [CollatzResearch.WordTrace]
  refine ⟨64742158152228399836269067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43161438768152266557512711 64742158152228399836269067)
  ·
    refine ⟨97113237228342599754403601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64742158152228399836269067 97113237228342599754403601)
    ·
      refine ⟨72834927921256949815802701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97113237228342599754403601 72834927921256949815802701)
      ·
        refine ⟨27313097970471356180926013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72834927921256949815802701 27313097970471356180926013)
        ·
          refine ⟨10242411738926758567847255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27313097970471356180926013 10242411738926758567847255)
          ·
            refine ⟨15363617608390137851770883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10242411738926758567847255 15363617608390137851770883)
            ·
              refine ⟨23045426412585206777656325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15363617608390137851770883 23045426412585206777656325)
              ·
                refine ⟨4321017452359726270810561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23045426412585206777656325 4321017452359726270810561)
                ·
                  refine ⟨3240763089269794703107921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4321017452359726270810561 3240763089269794703107921)
                  ·
                    refine ⟨2430572316952346027330941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3240763089269794703107921 2430572316952346027330941)
                    ·
                      refine ⟨911464618857129760249103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2430572316952346027330941 911464618857129760249103)
                      ·
                        rfl

theorem cell23_1775071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4, 2, 2, 3].length) (baseStart_1775071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1775071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1775071 prefixEnd_1775071 := by exact prefixLift 1775071
  have htrace : WordTrace (prefixWord ++ tailWord_1775071) baseStart_1775071 baseEnd_1775071 := by
    simpa [prefixWord, tailWord_1775071, baseEnd_1775071] using wordTrace_append hprefix tailTrace_1775071
  have hstable : (prefixWord ++ tailWord_1775071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775071).length < 2 ^ (prefixWord ++ tailWord_1775071).sum := by decide
  have hdescent : baseEnd_1775071 < baseStart_1775071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775085 : List Nat := [1, 5, 1, 3, 2, 1, 1, 1, 2, 4, 2]
def baseStart_1775085 : Nat := 118140960795 + 1775085 * 2 ^ 59
def prefixEnd_1775085 : Nat := 4983230072969 + 3 ^ 40 * 1775085 * 2
def baseEnd_1775085 : Nat := 911471807586292705474039

theorem tailTrace_1775085 : CollatzResearch.WordTrace tailWord_1775085 prefixEnd_1775085 911471807586292705474039 := by
  unfold tailWord_1775085
  simp only [CollatzResearch.WordTrace]
  refine ⟨64742668774177680227278709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43161779182785120151519139 64742668774177680227278709)
  ·
    refine ⟨6069625197579157521307379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64742668774177680227278709 6069625197579157521307379)
    ·
      refine ⟨9104437796368736281961069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6069625197579157521307379 9104437796368736281961069)
      ·
        refine ⟨3414164173638276105735401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9104437796368736281961069 3414164173638276105735401)
        ·
          refine ⟨2560623130228707079301551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3414164173638276105735401 2560623130228707079301551)
          ·
            refine ⟨3840934695343060618952327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2560623130228707079301551 3840934695343060618952327)
            ·
              refine ⟨5761402043014590928428491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3840934695343060618952327 5761402043014590928428491)
              ·
                refine ⟨8642103064521886392642737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5761402043014590928428491 8642103064521886392642737)
                ·
                  refine ⟨6481577298391414794482053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8642103064521886392642737 6481577298391414794482053)
                  ·
                    refine ⟨1215295743448390273965385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6481577298391414794482053 1215295743448390273965385)
                    ·
                      refine ⟨911471807586292705474039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1215295743448390273965385 911471807586292705474039)
                      ·
                        rfl

theorem cell23_1775085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_1775085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1775085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1775085 prefixEnd_1775085 := by exact prefixLift 1775085
  have htrace : WordTrace (prefixWord ++ tailWord_1775085) baseStart_1775085 baseEnd_1775085 := by
    simpa [prefixWord, tailWord_1775085, baseEnd_1775085] using wordTrace_append hprefix tailTrace_1775085
  have hstable : (prefixWord ++ tailWord_1775085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775085).length < 2 ^ (prefixWord ++ tailWord_1775085).sum := by decide
  have hdescent : baseEnd_1775085 < baseStart_1775085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775102 : List Nat := [4, 2, 2, 3, 1, 2, 1, 1, 2, 1, 4]
def baseStart_1775102 : Nat := 118140960795 + 1775102 * 2 ^ 59
def prefixEnd_1775102 : Nat := 4983230072969 + 3 ^ 40 * 1775102 * 2
def baseEnd_1775102 : Nat := 911480536757419138961461

theorem tailTrace_1775102 : CollatzResearch.WordTrace tailWord_1775102 prefixEnd_1775102 911480536757419138961461 := by
  unfold tailWord_1775102
  simp only [CollatzResearch.WordTrace]
  refine ⟨8092911101889511516330945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43162192543410728087098373 8092911101889511516330945)
  ·
    refine ⟨6069683326417133637248209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8092911101889511516330945 6069683326417133637248209)
    ·
      refine ⟨4552262494812850227936157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6069683326417133637248209 4552262494812850227936157)
      ·
        refine ⟨1707098435554818835476059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4552262494812850227936157 1707098435554818835476059)
        ·
          refine ⟨2560647653332228253214089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1707098435554818835476059 2560647653332228253214089)
          ·
            refine ⟨1920485739999171189910567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2560647653332228253214089 1920485739999171189910567)
            ·
              refine ⟨2880728609998756784865851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1920485739999171189910567 2880728609998756784865851)
              ·
                refine ⟨4321092914998135177298777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2880728609998756784865851 4321092914998135177298777)
                ·
                  refine ⟨3240819686248601382974083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4321092914998135177298777 3240819686248601382974083)
                  ·
                    refine ⟨4861229529372902074461125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3240819686248601382974083 4861229529372902074461125)
                    ·
                      refine ⟨911480536757419138961461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4861229529372902074461125 911480536757419138961461)
                      ·
                        rfl

theorem cell23_1775102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_1775102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1775102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1775102 prefixEnd_1775102 := by exact prefixLift 1775102
  have htrace : WordTrace (prefixWord ++ tailWord_1775102) baseStart_1775102 baseEnd_1775102 := by
    simpa [prefixWord, tailWord_1775102, baseEnd_1775102] using wordTrace_append hprefix tailTrace_1775102
  have hstable : (prefixWord ++ tailWord_1775102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775102).length < 2 ^ (prefixWord ++ tailWord_1775102).sum := by decide
  have hdescent : baseEnd_1775102 < baseStart_1775102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775105 : List Nat := [1, 2, 4, 1, 4, 2, 1, 1, 2, 2, 3]
def baseStart_1775105 : Nat := 118140960795 + 1775105 * 2 ^ 59
def prefixEnd_1775105 : Nat := 4983230072969 + 3 ^ 40 * 1775105 * 2
def baseEnd_1775105 : Nat := 911482077199382627223947

theorem tailTrace_1775105 : CollatzResearch.WordTrace tailWord_1775105 prefixEnd_1775105 911482077199382627223947 := by
  unfold tailWord_1775105
  simp only [CollatzResearch.WordTrace]
  refine ⟨64743398234105223643006769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43162265489403482428671179 64743398234105223643006769)
  ·
    refine ⟨48557548675578917732255077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64743398234105223643006769 48557548675578917732255077)
    ·
      refine ⟨9104540376671047074797827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48557548675578917732255077 9104540376671047074797827)
      ·
        refine ⟨13656810565006570612196741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9104540376671047074797827 13656810565006570612196741)
        ·
          refine ⟨2560651980938731989786889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13656810565006570612196741 2560651980938731989786889)
          ·
            refine ⟨1920488985704048992340167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2560651980938731989786889 1920488985704048992340167)
            ·
              refine ⟨2880733478556073488510251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1920488985704048992340167 2880733478556073488510251)
              ·
                refine ⟨4321100217834110232765377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2880733478556073488510251 4321100217834110232765377)
                ·
                  refine ⟨3240825163375582674574033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4321100217834110232765377 3240825163375582674574033)
                  ·
                    refine ⟨2430618872531687005930525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3240825163375582674574033 2430618872531687005930525)
                    ·
                      refine ⟨911482077199382627223947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2430618872531687005930525 911482077199382627223947)
                      ·
                        rfl

theorem cell23_1775105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_1775105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1775105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1775105 prefixEnd_1775105 := by exact prefixLift 1775105
  have htrace : WordTrace (prefixWord ++ tailWord_1775105) baseStart_1775105 baseEnd_1775105 := by
    simpa [prefixWord, tailWord_1775105, baseEnd_1775105] using wordTrace_append hprefix tailTrace_1775105
  have hstable : (prefixWord ++ tailWord_1775105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775105).length < 2 ^ (prefixWord ++ tailWord_1775105).sum := by decide
  have hdescent : baseEnd_1775105 < baseStart_1775105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775121 : List Nat := [1, 2, 2, 1, 1, 2, 5, 3, 1, 5]
def baseStart_1775121 : Nat := 118140960795 + 1775121 * 2 ^ 59
def prefixEnd_1775121 : Nat := 4983230072969 + 3 ^ 40 * 1775121 * 2
def baseEnd_1775121 : Nat := 303830097629951521541291

theorem tailTrace_1775121 : CollatzResearch.WordTrace tailWord_1775121 prefixEnd_1775121 303830097629951521541291 := by
  unfold tailWord_1775121
  simp only [CollatzResearch.WordTrace]
  refine ⟨64743981802047258375589217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43162654534698172250392811 64743981802047258375589217)
  ·
    refine ⟨48557986351535443781691913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64743981802047258375589217 48557986351535443781691913)
    ·
      refine ⟨36418489763651582836268935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48557986351535443781691913 36418489763651582836268935)
      ·
        refine ⟨54627734645477374254403403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36418489763651582836268935 54627734645477374254403403)
        ·
          refine ⟨81941601968216061381605105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54627734645477374254403403 81941601968216061381605105)
          ·
            refine ⟨61456201476162046036203829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81941601968216061381605105 61456201476162046036203829)
            ·
              refine ⟨5761518888390191815894109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61456201476162046036203829 5761518888390191815894109)
              ·
                refine ⟨2160569583146321930960291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5761518888390191815894109 2160569583146321930960291)
                ·
                  refine ⟨3240854374719482896440437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2160569583146321930960291 3240854374719482896440437)
                  ·
                    refine ⟨303830097629951521541291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3240854374719482896440437 303830097629951521541291)
                    ·
                      rfl

theorem cell23_1775121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 5].length) (baseStart_1775121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1775121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1775121 prefixEnd_1775121 := by exact prefixLift 1775121
  have htrace : WordTrace (prefixWord ++ tailWord_1775121) baseStart_1775121 baseEnd_1775121 := by
    simpa [prefixWord, tailWord_1775121, baseEnd_1775121] using wordTrace_append hprefix tailTrace_1775121
  have hstable : (prefixWord ++ tailWord_1775121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775121).length < 2 ^ (prefixWord ++ tailWord_1775121).sum := by decide
  have hdescent : baseEnd_1775121 < baseStart_1775121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775135 : List Nat := [1, 1, 2, 4, 1, 1, 4, 4, 1, 1, 3]
def baseStart_1775135 : Nat := 118140960795 + 1775135 * 2 ^ 59
def prefixEnd_1775135 : Nat := 4983230072969 + 3 ^ 40 * 1775135 * 2
def baseEnd_1775135 : Nat := 911497481619017509848809

theorem tailTrace_1775135 : CollatzResearch.WordTrace tailWord_1775135 prefixEnd_1775135 911497481619017509848809 := by
  unfold tailWord_1775135
  simp only [CollatzResearch.WordTrace]
  refine ⟨64744492423996538766598859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43162994949331025844399239 64744492423996538766598859)
  ·
    refine ⟨97116738635994808149898289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64744492423996538766598859 97116738635994808149898289)
    ·
      refine ⟨72837553976996106112423717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97116738635994808149898289 72837553976996106112423717)
      ·
        refine ⟨13657041370686769896079447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72837553976996106112423717 13657041370686769896079447)
        ·
          refine ⟨20485562056030154844119171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13657041370686769896079447 20485562056030154844119171)
          ·
            refine ⟨30728343084045232266178757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20485562056030154844119171 30728343084045232266178757)
            ·
              refine ⟨5761564328258481049908517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30728343084045232266178757 5761564328258481049908517)
              ·
                refine ⟨1080293311548465196857847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5761564328258481049908517 1080293311548465196857847)
                ·
                  refine ⟨1620439967322697795286771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1080293311548465196857847 1620439967322697795286771)
                  ·
                    refine ⟨2430659950984046692930157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1620439967322697795286771 2430659950984046692930157)
                    ·
                      refine ⟨911497481619017509848809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2430659950984046692930157 911497481619017509848809)
                      ·
                        rfl

theorem cell23_1775135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 4, 1, 1, 3].length) (baseStart_1775135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1775135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1775135 prefixEnd_1775135 := by exact prefixLift 1775135
  have htrace : WordTrace (prefixWord ++ tailWord_1775135) baseStart_1775135 baseEnd_1775135 := by
    simpa [prefixWord, tailWord_1775135, baseEnd_1775135] using wordTrace_append hprefix tailTrace_1775135
  have hstable : (prefixWord ++ tailWord_1775135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775135).length < 2 ^ (prefixWord ++ tailWord_1775135).sum := by decide
  have hdescent : baseEnd_1775135 < baseStart_1775135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775178 : List Nat := [3, 1, 2, 1, 1, 3, 1, 5, 1, 2, 3]
def baseStart_1775178 : Nat := 118140960795 + 1775178 * 2 ^ 59
def prefixEnd_1775178 : Nat := 4983230072969 + 3 ^ 40 * 1775178 * 2
def baseEnd_1775178 : Nat := 911519561287160841611111

theorem tailTrace_1775178 : CollatzResearch.WordTrace tailWord_1775178 prefixEnd_1775178 911519561287160841611111 := by
  unfold tailWord_1775178
  simp only [CollatzResearch.WordTrace]
  refine ⟨16186515190710189277603547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43164040508560504740276125 16186515190710189277603547)
  ·
    refine ⟨24279772786065283916405321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16186515190710189277603547 24279772786065283916405321)
    ·
      refine ⟨18209829589548962937303991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24279772786065283916405321 18209829589548962937303991)
      ·
        refine ⟨27314744384323444405955987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18209829589548962937303991 27314744384323444405955987)
        ·
          refine ⟨40972116576485166608933981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27314744384323444405955987 40972116576485166608933981)
          ·
            refine ⟨15364543716181937478350243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40972116576485166608933981 15364543716181937478350243)
            ·
              refine ⟨23046815574272906217525365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15364543716181937478350243 23046815574272906217525365)
              ·
                refine ⟨2160638960088084957893003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23046815574272906217525365 2160638960088084957893003)
                ·
                  refine ⟨3240958440132127436839505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2160638960088084957893003 3240958440132127436839505)
                  ·
                    refine ⟨2430718830099095577629629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3240958440132127436839505 2430718830099095577629629)
                    ·
                      refine ⟨911519561287160841611111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2430718830099095577629629 911519561287160841611111)
                      ·
                        rfl

theorem cell23_1775178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 5, 1, 2, 3].length) (baseStart_1775178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1775178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1775178 prefixEnd_1775178 := by exact prefixLift 1775178
  have htrace : WordTrace (prefixWord ++ tailWord_1775178) baseStart_1775178 baseEnd_1775178 := by
    simpa [prefixWord, tailWord_1775178, baseEnd_1775178] using wordTrace_append hprefix tailTrace_1775178
  have hstable : (prefixWord ++ tailWord_1775178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775178).length < 2 ^ (prefixWord ++ tailWord_1775178).sum := by decide
  have hdescent : baseEnd_1775178 < baseStart_1775178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775242 : List Nat := [3, 1, 2, 3, 2, 2, 2, 2, 2, 1, 3]
def baseStart_1775242 : Nat := 118140960795 + 1775242 * 2 ^ 59
def prefixEnd_1775242 : Nat := 4983230072969 + 3 ^ 40 * 1775242 * 2
def baseEnd_1775242 : Nat := 911552424049048591210817

theorem tailTrace_1775242 : CollatzResearch.WordTrace tailWord_1775242 prefixEnd_1775242 911552424049048591210817 := by
  unfold tailWord_1775242
  simp only [CollatzResearch.WordTrace]
  refine ⟨16187098758652224010185995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43165596689739264027162653 16187098758652224010185995)
  ·
    refine ⟨24280648137978336015278993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16187098758652224010185995 24280648137978336015278993)
    ·
      refine ⟨18210486103483752011459245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24280648137978336015278993 18210486103483752011459245)
      ·
        refine ⟨6828932288806407004297217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18210486103483752011459245 6828932288806407004297217)
        ·
          refine ⟨5121699216604805253222913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6828932288806407004297217 5121699216604805253222913)
          ·
            refine ⟨3841274412453603939917185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5121699216604805253222913 3841274412453603939917185)
            ·
              refine ⟨2880955809340202954937889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3841274412453603939917185 2880955809340202954937889)
              ·
                refine ⟨2160716857005152216203417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2880955809340202954937889 2160716857005152216203417)
                ·
                  refine ⟨1620537642753864162152563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2160716857005152216203417 1620537642753864162152563)
                  ·
                    refine ⟨2430806464130796243228845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1620537642753864162152563 2430806464130796243228845)
                    ·
                      refine ⟨911552424049048591210817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2430806464130796243228845 911552424049048591210817)
                      ·
                        rfl

theorem cell23_1775242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_1775242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1775242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1775242 prefixEnd_1775242 := by exact prefixLift 1775242
  have htrace : WordTrace (prefixWord ++ tailWord_1775242) baseStart_1775242 baseEnd_1775242 := by
    simpa [prefixWord, tailWord_1775242, baseEnd_1775242] using wordTrace_append hprefix tailTrace_1775242
  have hstable : (prefixWord ++ tailWord_1775242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775242).length < 2 ^ (prefixWord ++ tailWord_1775242).sum := by decide
  have hdescent : baseEnd_1775242 < baseStart_1775242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775265 : List Nat := [1, 2, 3, 3, 2, 1, 1, 3, 1, 4, 2]
def baseStart_1775265 : Nat := 118140960795 + 1775265 * 2 ^ 59
def prefixEnd_1775265 : Nat := 4983230072969 + 3 ^ 40 * 1775265 * 2
def baseEnd_1775265 : Nat := 911564234104102001223211

theorem tailTrace_1775265 : CollatzResearch.WordTrace tailWord_1775265 prefixEnd_1775265 911564234104102001223211 := by
  unfold tailWord_1775265
  simp only [CollatzResearch.WordTrace]
  refine ⟨64749233913525570968831249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43166155942350380645887499 64749233913525570968831249)
  ·
    refine ⟨48561925435144178226623437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64749233913525570968831249 48561925435144178226623437)
    ·
      refine ⟨18210722038179066834983789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48561925435144178226623437 18210722038179066834983789)
      ·
        refine ⟨6829020764317150063118921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18210722038179066834983789 6829020764317150063118921)
        ·
          refine ⟨5121765573237862547339191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6829020764317150063118921 5121765573237862547339191)
          ·
            refine ⟨7682648359856793821008787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5121765573237862547339191 7682648359856793821008787)
            ·
              refine ⟨11523972539785190731513181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7682648359856793821008787 11523972539785190731513181)
              ·
                refine ⟨4321489702419446524317443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11523972539785190731513181 4321489702419446524317443)
                ·
                  refine ⟨6482234553629169786476165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4321489702419446524317443 6482234553629169786476165)
                  ·
                    refine ⟨1215418978805469334964281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6482234553629169786476165 1215418978805469334964281)
                    ·
                      refine ⟨911564234104102001223211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1215418978805469334964281 911564234104102001223211)
                      ·
                        rfl

theorem cell23_1775265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_1775265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1775265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1775265 prefixEnd_1775265 := by exact prefixLift 1775265
  have htrace : WordTrace (prefixWord ++ tailWord_1775265) baseStart_1775265 baseEnd_1775265 := by
    simpa [prefixWord, tailWord_1775265, baseEnd_1775265] using wordTrace_append hprefix tailTrace_1775265
  have hstable : (prefixWord ++ tailWord_1775265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775265).length < 2 ^ (prefixWord ++ tailWord_1775265).sum := by decide
  have hdescent : baseEnd_1775265 < baseStart_1775265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775286 : List Nat := [5, 1, 3, 1, 1, 1, 4, 1, 1, 3, 2]
def baseStart_1775286 : Nat := 118140960795 + 1775286 * 2 ^ 59
def prefixEnd_1775286 : Nat := 4983230072969 + 3 ^ 40 * 1775286 * 2
def baseEnd_1775286 : Nat := 911575017197846419060615

theorem tailTrace_1775286 : CollatzResearch.WordTrace tailWord_1775286 prefixEnd_1775286 911575017197846419060615 := by
  unfold tailWord_1775286
  simp only [CollatzResearch.WordTrace]
  refine ⟨4046874990403093222209107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43166666564299661036897141 4046874990403093222209107)
  ·
    refine ⟨6070312485604639833313661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4046874990403093222209107 6070312485604639833313661)
    ·
      refine ⟨2276367182101739937492623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6070312485604639833313661 2276367182101739937492623)
      ·
        refine ⟨3414550773152609906238935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2276367182101739937492623 3414550773152609906238935)
        ·
          refine ⟨5121826159728914859358403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3414550773152609906238935 5121826159728914859358403)
          ·
            refine ⟨7682739239593372289037605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5121826159728914859358403 7682739239593372289037605)
            ·
              refine ⟨1440513607423757304194551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7682739239593372289037605 1440513607423757304194551)
              ·
                refine ⟨2160770411135635956291827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1440513607423757304194551 2160770411135635956291827)
                ·
                  refine ⟨3241155616703453934437741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2160770411135635956291827 3241155616703453934437741)
                  ·
                    refine ⟨1215433356263795225414153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3241155616703453934437741 1215433356263795225414153)
                    ·
                      refine ⟨911575017197846419060615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1215433356263795225414153 911575017197846419060615)
                      ·
                        rfl

theorem cell23_1775286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_1775286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1775286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1775286 prefixEnd_1775286 := by exact prefixLift 1775286
  have htrace : WordTrace (prefixWord ++ tailWord_1775286) baseStart_1775286 baseEnd_1775286 := by
    simpa [prefixWord, tailWord_1775286, baseEnd_1775286] using wordTrace_append hprefix tailTrace_1775286
  have hstable : (prefixWord ++ tailWord_1775286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775286).length < 2 ^ (prefixWord ++ tailWord_1775286).sum := by decide
  have hdescent : baseEnd_1775286 < baseStart_1775286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775311 : List Nat := [1, 1, 2, 1, 1, 3, 1, 5, 1, 2, 5]
def baseStart_1775311 : Nat := 118140960795 + 1775311 * 2 ^ 59
def prefixEnd_1775311 : Nat := 4983230072969 + 3 ^ 40 * 1775311 * 2
def baseEnd_1775311 : Nat := 911587854214208821247999

theorem tailTrace_1775311 : CollatzResearch.WordTrace tailWord_1775311 prefixEnd_1775311 911587854214208821247999 := by
  unfold tailWord_1775311
  simp only [CollatzResearch.WordTrace]
  refine ⟨64750911671358920825005787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43167274447572613883337191 64750911671358920825005787)
  ·
    refine ⟨97126367507038381237508681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64750911671358920825005787 97126367507038381237508681)
    ·
      refine ⟨72844775630278785928131511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97126367507038381237508681 72844775630278785928131511)
      ·
        refine ⟨109267163445418178892197267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72844775630278785928131511 109267163445418178892197267)
        ·
          refine ⟨163900745168127268338295901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109267163445418178892197267 163900745168127268338295901)
          ·
            refine ⟨61462779438047725626860963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163900745168127268338295901 61462779438047725626860963)
            ·
              refine ⟨92194169157071588440291445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61462779438047725626860963 92194169157071588440291445)
              ·
                refine ⟨8643203358475461416277323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92194169157071588440291445 8643203358475461416277323)
                ·
                  refine ⟨12964805037713192124415985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8643203358475461416277323 12964805037713192124415985)
                  ·
                    refine ⟨9723603778284894093311989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12964805037713192124415985 9723603778284894093311989)
                    ·
                      refine ⟨911587854214208821247999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9723603778284894093311989 911587854214208821247999)
                      ·
                        rfl

theorem cell23_1775311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 2, 5].length) (baseStart_1775311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1775311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1775311 prefixEnd_1775311 := by exact prefixLift 1775311
  have htrace : WordTrace (prefixWord ++ tailWord_1775311) baseStart_1775311 baseEnd_1775311 := by
    simpa [prefixWord, tailWord_1775311, baseEnd_1775311] using wordTrace_append hprefix tailTrace_1775311
  have hstable : (prefixWord ++ tailWord_1775311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775311).length < 2 ^ (prefixWord ++ tailWord_1775311).sum := by decide
  have hdescent : baseEnd_1775311 < baseStart_1775311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775316 : List Nat := [2, 4, 1, 3, 1, 2, 3, 1, 2, 2, 2]
def baseStart_1775316 : Nat := 118140960795 + 1775316 * 2 ^ 59
def prefixEnd_1775316 : Nat := 4983230072969 + 3 ^ 40 * 1775316 * 2
def baseEnd_1775316 : Nat := 911590421617481301685477

theorem tailTrace_1775316 : CollatzResearch.WordTrace tailWord_1775316 prefixEnd_1775316 911590421617481301685477 := by
  unfold tailWord_1775316
  simp only [CollatzResearch.WordTrace]
  refine ⟨32375547018170403339468901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43167396024227204452625201 32375547018170403339468901)
  ·
    refine ⟨6070415065906950626150419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32375547018170403339468901 6070415065906950626150419)
    ·
      refine ⟨9105622598860425939225629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6070415065906950626150419 9105622598860425939225629)
      ·
        refine ⟨3414608474572659727209611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9105622598860425939225629 3414608474572659727209611)
        ·
          refine ⟨5121912711858989590814417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3414608474572659727209611 5121912711858989590814417)
          ·
            refine ⟨3841434533894242193110813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5121912711858989590814417 3841434533894242193110813)
            ·
              refine ⟨1440537950210340822416555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3841434533894242193110813 1440537950210340822416555)
              ·
                refine ⟨2160806925315511233624833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1440537950210340822416555 2160806925315511233624833)
                ·
                  refine ⟨1620605193986633425218625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2160806925315511233624833 1620605193986633425218625)
                  ·
                    refine ⟨1215453895489975068913969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1620605193986633425218625 1215453895489975068913969)
                    ·
                      refine ⟨911590421617481301685477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1215453895489975068913969 911590421617481301685477)
                      ·
                        rfl

theorem cell23_1775316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_1775316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1775316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1775316 prefixEnd_1775316 := by exact prefixLift 1775316
  have htrace : WordTrace (prefixWord ++ tailWord_1775316) baseStart_1775316 baseEnd_1775316 := by
    simpa [prefixWord, tailWord_1775316, baseEnd_1775316] using wordTrace_append hprefix tailTrace_1775316
  have hstable : (prefixWord ++ tailWord_1775316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775316).length < 2 ^ (prefixWord ++ tailWord_1775316).sum := by decide
  have hdescent : baseEnd_1775316 < baseStart_1775316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775338 : List Nat := [3, 1, 3, 1, 1, 1, 4, 1, 1, 3, 4]
def baseStart_1775338 : Nat := 118140960795 + 1775338 * 2 ^ 59
def prefixEnd_1775338 : Nat := 4983230072969 + 3 ^ 40 * 1775338 * 2
def baseEnd_1775338 : Nat := 911601718191880215610375

theorem tailTrace_1775338 : CollatzResearch.WordTrace tailWord_1775338 prefixEnd_1775338 911601718191880215610375 := by
  unfold tailWord_1775338
  simp only [CollatzResearch.WordTrace]
  refine ⟨16187974110565276109059667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43167930961507402957492445 16187974110565276109059667)
  ·
    refine ⟨24281961165847914163589501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16187974110565276109059667 24281961165847914163589501)
    ·
      refine ⟨9105735437192967811346063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24281961165847914163589501 9105735437192967811346063)
      ·
        refine ⟨13658603155789451717019095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9105735437192967811346063 13658603155789451717019095)
        ·
          refine ⟨20487904733684177575528643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13658603155789451717019095 20487904733684177575528643)
          ·
            refine ⟨30731857100526266363292965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20487904733684177575528643 30731857100526266363292965)
            ·
              refine ⟨5762223206348674943117431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30731857100526266363292965 5762223206348674943117431)
              ·
                refine ⟨8643334809523012414676147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5762223206348674943117431 8643334809523012414676147)
                ·
                  refine ⟨12965002214284518622014221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8643334809523012414676147 12965002214284518622014221)
                  ·
                    refine ⟨4861875830356694483255333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12965002214284518622014221 4861875830356694483255333)
                    ·
                      refine ⟨911601718191880215610375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4861875830356694483255333 911601718191880215610375)
                      ·
                        rfl

theorem cell23_1775338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_1775338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1775338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1775338 prefixEnd_1775338 := by exact prefixLift 1775338
  have htrace : WordTrace (prefixWord ++ tailWord_1775338) baseStart_1775338 baseEnd_1775338 := by
    simpa [prefixWord, tailWord_1775338, baseEnd_1775338] using wordTrace_append hprefix tailTrace_1775338
  have hstable : (prefixWord ++ tailWord_1775338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775338).length < 2 ^ (prefixWord ++ tailWord_1775338).sum := by decide
  have hdescent : baseEnd_1775338 < baseStart_1775338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775351 : List Nat := [1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 6]
def baseStart_1775351 : Nat := 118140960795 + 1775351 * 2 ^ 59
def prefixEnd_1775351 : Nat := 4983230072969 + 3 ^ 40 * 1775351 * 2
def baseEnd_1775351 : Nat := 911608393440388664747815

theorem tailTrace_1775351 : CollatzResearch.WordTrace tailWord_1775351 prefixEnd_1775351 911608393440388664747815 := by
  unfold tailWord_1775351
  simp only [CollatzResearch.WordTrace]
  refine ⟨64752370591214007656461907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43168247060809338437641271 64752370591214007656461907)
  ·
    refine ⟨97128555886821011484692861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64752370591214007656461907 97128555886821011484692861)
    ·
      refine ⟨36423208457557879306759823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97128555886821011484692861 36423208457557879306759823)
      ·
        refine ⟨54634812686336818960139735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36423208457557879306759823 54634812686336818960139735)
        ·
          refine ⟨81952219029505228440209603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54634812686336818960139735 81952219029505228440209603)
          ·
            refine ⟨122928328544257842660314405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81952219029505228440209603 122928328544257842660314405)
            ·
              refine ⟨23049061602048345498808951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122928328544257842660314405 23049061602048345498808951)
              ·
                refine ⟨34573592403072518248213427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23049061602048345498808951 34573592403072518248213427)
                ·
                  refine ⟨51860388604608777372320141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34573592403072518248213427 51860388604608777372320141)
                  ·
                    refine ⟨19447645726728291514620053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51860388604608777372320141 19447645726728291514620053)
                    ·
                      refine ⟨911608393440388664747815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19447645726728291514620053 911608393440388664747815)
                      ·
                        rfl

theorem cell23_1775351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 6].length) (baseStart_1775351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1775351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1775351 prefixEnd_1775351 := by exact prefixLift 1775351
  have htrace : WordTrace (prefixWord ++ tailWord_1775351) baseStart_1775351 baseEnd_1775351 := by
    simpa [prefixWord, tailWord_1775351, baseEnd_1775351] using wordTrace_append hprefix tailTrace_1775351
  have hstable : (prefixWord ++ tailWord_1775351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775351).length < 2 ^ (prefixWord ++ tailWord_1775351).sum := by decide
  have hdescent : baseEnd_1775351 < baseStart_1775351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775412 : List Nat := [2, 5, 1, 1, 2, 2, 2, 2, 6]
def baseStart_1775412 : Nat := 118140960795 + 1775412 * 2 ^ 59
def prefixEnd_1775412 : Nat := 4983230072969 + 3 ^ 40 * 1775412 * 2
def baseEnd_1775412 : Nat := 101293301751145880676115

theorem tailTrace_1775412 : CollatzResearch.WordTrace tailWord_1775412 prefixEnd_1775412 101293301751145880676115 := by
  unfold tailWord_1775412
  simp only [CollatzResearch.WordTrace]
  refine ⟨32377297721996507537216245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43169730295995343382954993 32377297721996507537216245)
  ·
    refine ⟨3035371661437172581614023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32377297721996507537216245 3035371661437172581614023)
    ·
      refine ⟨4553057492155758872421035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3035371661437172581614023 4553057492155758872421035)
      ·
        refine ⟨6829586238233638308631553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4553057492155758872421035 6829586238233638308631553)
        ·
          refine ⟨5122189678675228731473665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6829586238233638308631553 5122189678675228731473665)
          ·
            refine ⟨3841642259006421548605249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5122189678675228731473665 3841642259006421548605249)
            ·
              refine ⟨2881231694254816161453937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3841642259006421548605249 2881231694254816161453937)
              ·
                refine ⟨2160923770691112121090453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2881231694254816161453937 2160923770691112121090453)
                ·
                  refine ⟨101293301751145880676115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2160923770691112121090453 101293301751145880676115)
                  ·
                    rfl

theorem cell23_1775412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_1775412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1775412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1775412 prefixEnd_1775412 := by exact prefixLift 1775412
  have htrace : WordTrace (prefixWord ++ tailWord_1775412) baseStart_1775412 baseEnd_1775412 := by
    simpa [prefixWord, tailWord_1775412, baseEnd_1775412] using wordTrace_append hprefix tailTrace_1775412
  have hstable : (prefixWord ++ tailWord_1775412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775412).length < 2 ^ (prefixWord ++ tailWord_1775412).sum := by decide
  have hdescent : baseEnd_1775412 < baseStart_1775412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775415 : List Nat := [1, 1, 3, 1, 2, 1, 2, 3, 4, 3, 2]
def baseStart_1775415 : Nat := 118140960795 + 1775415 * 2 ^ 59
def prefixEnd_1775415 : Nat := 4983230072969 + 3 ^ 40 * 1775415 * 2
def baseEnd_1775415 : Nat := 911641256202276414347521

theorem tailTrace_1775415 : CollatzResearch.WordTrace tailWord_1775415 prefixEnd_1775415 911641256202276414347521 := by
  unfold tailWord_1775415
  simp only [CollatzResearch.WordTrace]
  refine ⟨64754704862982146586791699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43169803241988097724527799 64754704862982146586791699)
  ·
    refine ⟨97132057294473219880187549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64754704862982146586791699 97132057294473219880187549)
    ·
      refine ⟨36424521485427457455070331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97132057294473219880187549 36424521485427457455070331)
      ·
        refine ⟨54636782228141186182605497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36424521485427457455070331 54636782228141186182605497)
        ·
          refine ⟨40977586671105889636954123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54636782228141186182605497 40977586671105889636954123)
          ·
            refine ⟨61466380006658834455431185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40977586671105889636954123 61466380006658834455431185)
            ·
              refine ⟨46099785004994125841573389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61466380006658834455431185 46099785004994125841573389)
              ·
                refine ⟨17287419376872797190590021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46099785004994125841573389 17287419376872797190590021)
                ·
                  refine ⟨3241391133163649473235629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17287419376872797190590021 3241391133163649473235629)
                  ·
                    refine ⟨1215521674936368552463361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3241391133163649473235629 1215521674936368552463361)
                    ·
                      refine ⟨911641256202276414347521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1215521674936368552463361 911641256202276414347521)
                      ·
                        rfl

theorem cell23_1775415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 4, 3, 2].length) (baseStart_1775415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1775415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1775415 prefixEnd_1775415 := by exact prefixLift 1775415
  have htrace : WordTrace (prefixWord ++ tailWord_1775415) baseStart_1775415 baseEnd_1775415 := by
    simpa [prefixWord, tailWord_1775415, baseEnd_1775415] using wordTrace_append hprefix tailTrace_1775415
  have hstable : (prefixWord ++ tailWord_1775415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775415).length < 2 ^ (prefixWord ++ tailWord_1775415).sum := by decide
  have hdescent : baseEnd_1775415 < baseStart_1775415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775445 : List Nat := [1, 3, 2, 2, 2, 2, 2, 1, 3, 1, 4]
def baseStart_1775445 : Nat := 118140960795 + 1775445 * 2 ^ 59
def prefixEnd_1775445 : Nat := 4983230072969 + 3 ^ 40 * 1775445 * 2
def baseEnd_1775445 : Nat := 911656660621911296972383

theorem tailTrace_1775445 : CollatzResearch.WordTrace tailWord_1775445 prefixEnd_1775445 911656660621911296972383 := by
  unfold tailWord_1775445
  simp only [CollatzResearch.WordTrace]
  refine ⟨64755799052873461710383789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43170532701915641140255859 64755799052873461710383789)
  ·
    refine ⟨24283424644827548141393921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64755799052873461710383789 24283424644827548141393921)
    ·
      refine ⟨18212568483620661106045441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24283424644827548141393921 18212568483620661106045441)
      ·
        refine ⟨13659426362715495829534081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18212568483620661106045441 13659426362715495829534081)
        ·
          refine ⟨10244569772036621872150561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13659426362715495829534081 10244569772036621872150561)
          ·
            refine ⟨7683427329027466404112921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10244569772036621872150561 7683427329027466404112921)
            ·
              refine ⟨5762570496770599803084691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7683427329027466404112921 5762570496770599803084691)
              ·
                refine ⟨8643855745155899704627037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5762570496770599803084691 8643855745155899704627037)
                ·
                  refine ⟨3241445904433462389235139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8643855745155899704627037 3241445904433462389235139)
                  ·
                    refine ⟨4862168856650193583852709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3241445904433462389235139 4862168856650193583852709)
                    ·
                      refine ⟨911656660621911296972383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4862168856650193583852709 911656660621911296972383)
                      ·
                        rfl

theorem cell23_1775445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_1775445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1775445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1775445 prefixEnd_1775445 := by exact prefixLift 1775445
  have htrace : WordTrace (prefixWord ++ tailWord_1775445) baseStart_1775445 baseEnd_1775445 := by
    simpa [prefixWord, tailWord_1775445, baseEnd_1775445] using wordTrace_append hprefix tailTrace_1775445
  have hstable : (prefixWord ++ tailWord_1775445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775445).length < 2 ^ (prefixWord ++ tailWord_1775445).sum := by decide
  have hdescent : baseEnd_1775445 < baseStart_1775445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775459 : List Nat := [1, 1, 1, 5, 4, 2, 2, 1, 1, 5]
def baseStart_1775459 : Nat := 118140960795 + 1775459 * 2 ^ 59
def prefixEnd_1775459 : Nat := 4983230072969 + 3 ^ 40 * 1775459 * 2
def baseEnd_1775459 : Nat := 303887949783691414065773

theorem tailTrace_1775459 : CollatzResearch.WordTrace tailWord_1775459 prefixEnd_1775459 303887949783691414065773 := by
  unfold tailWord_1775459
  simp only [CollatzResearch.WordTrace]
  refine ⟨64756309674822742101393431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43170873116548494734262287 64756309674822742101393431)
  ·
    refine ⟨97134464512234113152090147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64756309674822742101393431 97134464512234113152090147)
    ·
      refine ⟨145701696768351169728135221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97134464512234113152090147 145701696768351169728135221)
      ·
        refine ⟨13659534072032922162012677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 145701696768351169728135221 13659534072032922162012677)
        ·
          refine ⟨2561162638506172905377377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13659534072032922162012677 2561162638506172905377377)
          ·
            refine ⟨1920871978879629679033033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2561162638506172905377377 1920871978879629679033033)
            ·
              refine ⟨1440653984159722259274775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1920871978879629679033033 1440653984159722259274775)
              ·
                refine ⟨2160980976239583388912163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1440653984159722259274775 2160980976239583388912163)
                ·
                  refine ⟨3241471464359375083368245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2160980976239583388912163 3241471464359375083368245)
                  ·
                    refine ⟨303887949783691414065773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3241471464359375083368245 303887949783691414065773)
                    ·
                      rfl

theorem cell23_1775459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 1, 1, 5].length) (baseStart_1775459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1775459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1775459 prefixEnd_1775459 := by exact prefixLift 1775459
  have htrace : WordTrace (prefixWord ++ tailWord_1775459) baseStart_1775459 baseEnd_1775459 := by
    simpa [prefixWord, tailWord_1775459, baseEnd_1775459] using wordTrace_append hprefix tailTrace_1775459
  have hstable : (prefixWord ++ tailWord_1775459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775459).length < 2 ^ (prefixWord ++ tailWord_1775459).sum := by decide
  have hdescent : baseEnd_1775459 < baseStart_1775459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775468 : List Nat := [2, 2, 1, 1, 4, 3, 10]
def baseStart_1775468 : Nat := 118140960795 + 1775468 * 2 ^ 59
def prefixEnd_1775468 : Nat := 4983230072969 + 3 ^ 40 * 1775468 * 2
def baseEnd_1775468 : Nat := 11255166304653885271417

theorem tailTrace_1775468 : CollatzResearch.WordTrace tailWord_1775468 prefixEnd_1775468 11255166304653885271417 := by
  unfold tailWord_1775468
  simp only [CollatzResearch.WordTrace]
  refine ⟨32378318965895068319235529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43171091954526757758980705 32378318965895068319235529)
  ·
    refine ⟨24283739224421301239426647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32378318965895068319235529 24283739224421301239426647)
    ·
      refine ⟨36425608836631951859139971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24283739224421301239426647 36425608836631951859139971)
      ·
        refine ⟨54638413254947927788709957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36425608836631951859139971 54638413254947927788709957)
        ·
          refine ⟨10244702485302736460383117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54638413254947927788709957 10244702485302736460383117)
          ·
            refine ⟨3841763431988526172643669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10244702485302736460383117 3841763431988526172643669)
            ·
              refine ⟨11255166304653885271417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3841763431988526172643669 11255166304653885271417)
              ·
                rfl

theorem cell23_1775468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 10].length) (baseStart_1775468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1775468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1775468 prefixEnd_1775468 := by exact prefixLift 1775468
  have htrace : WordTrace (prefixWord ++ tailWord_1775468) baseStart_1775468 baseEnd_1775468 := by
    simpa [prefixWord, tailWord_1775468, baseEnd_1775468] using wordTrace_append hprefix tailTrace_1775468
  have hstable : (prefixWord ++ tailWord_1775468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775468).length < 2 ^ (prefixWord ++ tailWord_1775468).sum := by decide
  have hdescent : baseEnd_1775468 < baseStart_1775468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775489 : List Nat := [1, 2, 4, 4, 1, 2, 1, 1, 1, 6]
def baseStart_1775489 : Nat := 118140960795 + 1775489 * 2 ^ 59
def prefixEnd_1775489 : Nat := 4983230072969 + 3 ^ 40 * 1775489 * 2
def baseEnd_1775489 : Nat := 303893084590236374940727

theorem tailTrace_1775489 : CollatzResearch.WordTrace tailWord_1775489 prefixEnd_1775489 303893084590236374940727 := by
  unfold tailWord_1775489
  simp only [CollatzResearch.WordTrace]
  refine ⟨64757403864714057224985521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43171602576476038149990347 64757403864714057224985521)
  ·
    refine ⟨48568052898535542918739141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64757403864714057224985521 48568052898535542918739141)
    ·
      refine ⟨9106509918475414297263589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48568052898535542918739141 9106509918475414297263589)
      ·
        refine ⟨1707470609714140180736923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9106509918475414297263589 1707470609714140180736923)
        ·
          refine ⟨2561205914571210271105385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1707470609714140180736923 2561205914571210271105385)
          ·
            refine ⟨1920904435928407703329039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2561205914571210271105385 1920904435928407703329039)
            ·
              refine ⟨2881356653892611554993559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1920904435928407703329039 2881356653892611554993559)
              ·
                refine ⟨4322034980838917332490339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2881356653892611554993559 4322034980838917332490339)
                ·
                  refine ⟨6483052471258375998735509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4322034980838917332490339 6483052471258375998735509)
                  ·
                    refine ⟨303893084590236374940727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6483052471258375998735509 303893084590236374940727)
                    ·
                      rfl

theorem cell23_1775489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_1775489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1775489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1775489 prefixEnd_1775489 := by exact prefixLift 1775489
  have htrace : WordTrace (prefixWord ++ tailWord_1775489) baseStart_1775489 baseEnd_1775489 := by
    simpa [prefixWord, tailWord_1775489, baseEnd_1775489] using wordTrace_append hprefix tailTrace_1775489
  have hstable : (prefixWord ++ tailWord_1775489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775489).length < 2 ^ (prefixWord ++ tailWord_1775489).sum := by decide
  have hdescent : baseEnd_1775489 < baseStart_1775489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775502 : List Nat := [4, 1, 1, 5, 1, 1, 1, 9]
def baseStart_1775502 : Nat := 118140960795 + 1775502 * 2 ^ 59
def prefixEnd_1775502 : Nat := 4983230072969 + 3 ^ 40 * 1775502 * 2
def baseEnd_1775502 : Nat := 33766145519230280517023

theorem tailTrace_1775502 : CollatzResearch.WordTrace tailWord_1775502 prefixEnd_1775502 33766145519230280517023 := by
  unfold tailWord_1775502
  simp only [CollatzResearch.WordTrace]
  refine ⟨8094734751708370055651095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43171918675777973630139173 8094734751708370055651095)
  ·
    refine ⟨12142102127562555083476643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8094734751708370055651095 12142102127562555083476643)
    ·
      refine ⟨18213153191343832625214965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12142102127562555083476643 18213153191343832625214965)
      ·
        refine ⟨1707483111688484308613903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18213153191343832625214965 1707483111688484308613903)
        ·
          refine ⟨2561224667532726462920855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1707483111688484308613903 2561224667532726462920855)
          ·
            refine ⟨3841837001299089694381283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2561224667532726462920855 3841837001299089694381283)
            ·
              refine ⟨5762755501948634541571925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3841837001299089694381283 5762755501948634541571925)
              ·
                refine ⟨33766145519230280517023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5762755501948634541571925 33766145519230280517023)
                ·
                  rfl

theorem cell23_1775502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 9].length) (baseStart_1775502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1775502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1775502 prefixEnd_1775502 := by exact prefixLift 1775502
  have htrace : WordTrace (prefixWord ++ tailWord_1775502) baseStart_1775502 baseEnd_1775502 := by
    simpa [prefixWord, tailWord_1775502, baseEnd_1775502] using wordTrace_append hprefix tailTrace_1775502
  have hstable : (prefixWord ++ tailWord_1775502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775502).length < 2 ^ (prefixWord ++ tailWord_1775502).sum := by decide
  have hdescent : baseEnd_1775502 < baseStart_1775502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775540 : List Nat := [2, 5, 2, 1, 3, 1, 2, 1, 2, 4]
def baseStart_1775540 : Nat := 118140960795 + 1775540 * 2 ^ 59
def prefixEnd_1775540 : Nat := 4983230072969 + 3 ^ 40 * 1775540 * 2
def baseEnd_1775540 : Nat := 303901813761362808428149

theorem tailTrace_1775540 : CollatzResearch.WordTrace tailWord_1775540 prefixEnd_1775540 303901813761362808428149 := by
  unfold tailWord_1775540
  simp only [CollatzResearch.WordTrace]
  refine ⟨32379631993764646467546037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43172842658352861956728049 32379631993764646467546037)
  ·
    refine ⟨3035590499415435606332441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32379631993764646467546037 3035590499415435606332441)
    ·
      refine ⟨2276692874561576704749331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3035590499415435606332441 2276692874561576704749331)
      ·
        refine ⟨3415039311842365057123997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2276692874561576704749331 3415039311842365057123997)
        ·
          refine ⟨1280639741940886896421499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3415039311842365057123997 1280639741940886896421499)
          ·
            refine ⟨1920959612911330344632249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1280639741940886896421499 1920959612911330344632249)
            ·
              refine ⟨1440719709683497758474187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1920959612911330344632249 1440719709683497758474187)
              ·
                refine ⟨2161079564525246637711281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1440719709683497758474187 2161079564525246637711281)
                ·
                  refine ⟨1620809673393934978283461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2161079564525246637711281 1620809673393934978283461)
                  ·
                    refine ⟨303901813761362808428149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1620809673393934978283461 303901813761362808428149)
                    ·
                      rfl

theorem cell23_1775540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_1775540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1775540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1775540 prefixEnd_1775540 := by exact prefixLift 1775540
  have htrace : WordTrace (prefixWord ++ tailWord_1775540) baseStart_1775540 baseEnd_1775540 := by
    simpa [prefixWord, tailWord_1775540, baseEnd_1775540] using wordTrace_append hprefix tailTrace_1775540
  have hstable : (prefixWord ++ tailWord_1775540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775540).length < 2 ^ (prefixWord ++ tailWord_1775540).sum := by decide
  have hdescent : baseEnd_1775540 < baseStart_1775540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775552 : List Nat := [2, 1, 1, 2, 3, 2, 2, 3, 1, 4, 2]
def baseStart_1775552 : Nat := 118140960795 + 1775552 * 2 ^ 59
def prefixEnd_1775552 : Nat := 4983230072969 + 3 ^ 40 * 1775552 * 2
def baseEnd_1775552 : Nat := 911711603051942378334391

theorem tailTrace_1775552 : CollatzResearch.WordTrace tailWord_1775552 prefixEnd_1775552 911711603051942378334391 := by
  unfold tailWord_1775552
  simp only [CollatzResearch.WordTrace]
  refine ⟨32379850831742909492264455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43173134442323879323019273 32379850831742909492264455)
  ·
    refine ⟨48569776247614364238396683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32379850831742909492264455 48569776247614364238396683)
    ·
      refine ⟨72854664371421546357595025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48569776247614364238396683 72854664371421546357595025)
      ·
        refine ⟨54640998278566159768196269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72854664371421546357595025 54640998278566159768196269)
        ·
          refine ⟨20490374354462309913073601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54640998278566159768196269 20490374354462309913073601)
          ·
            refine ⟨15367780765846732434805201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20490374354462309913073601 15367780765846732434805201)
            ·
              refine ⟨11525835574385049326103901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15367780765846732434805201 11525835574385049326103901)
              ·
                refine ⟨4322188340394393497288963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11525835574385049326103901 4322188340394393497288963)
                ·
                  refine ⟨6483282510591590245933445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4322188340394393497288963 6483282510591590245933445)
                  ·
                    refine ⟨1215615470735923171112521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6483282510591590245933445 1215615470735923171112521)
                    ·
                      refine ⟨911711603051942378334391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1215615470735923171112521 911711603051942378334391)
                      ·
                        rfl

theorem cell23_1775552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3, 1, 4, 2].length) (baseStart_1775552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1775552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1775552 prefixEnd_1775552 := by exact prefixLift 1775552
  have htrace : WordTrace (prefixWord ++ tailWord_1775552) baseStart_1775552 baseEnd_1775552 := by
    simpa [prefixWord, tailWord_1775552, baseEnd_1775552] using wordTrace_append hprefix tailTrace_1775552
  have hstable : (prefixWord ++ tailWord_1775552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775552).length < 2 ^ (prefixWord ++ tailWord_1775552).sum := by decide
  have hdescent : baseEnd_1775552 < baseStart_1775552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775580 : List Nat := [2, 2, 6, 1, 1, 1, 2, 2, 2, 1, 3]
def baseStart_1775580 : Nat := 118140960795 + 1775580 * 2 ^ 59
def prefixEnd_1775580 : Nat := 4983230072969 + 3 ^ 40 * 1775580 * 2
def baseEnd_1775580 : Nat := 911725980510268268784263

theorem tailTrace_1775580 : CollatzResearch.WordTrace tailWord_1775580 prefixEnd_1775580 911725980510268268784263 := by
  unfold tailWord_1775580
  simp only [CollatzResearch.WordTrace]
  refine ⟨32380361453692189883274097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43173815271589586511032129 32380361453692189883274097)
  ·
    refine ⟨24285271090269142412455573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32380361453692189883274097 24285271090269142412455573)
    ·
      refine ⟨1138372082356366050583855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24285271090269142412455573 1138372082356366050583855)
      ·
        refine ⟨1707558123534549075875783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1138372082356366050583855 1707558123534549075875783)
        ·
          refine ⟨2561337185301823613813675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1707558123534549075875783 2561337185301823613813675)
          ·
            refine ⟨3842005777952735420720513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2561337185301823613813675 3842005777952735420720513)
            ·
              refine ⟨2881504333464551565540385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3842005777952735420720513 2881504333464551565540385)
              ·
                refine ⟨2161128250098413674155289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2881504333464551565540385 2161128250098413674155289)
                ·
                  refine ⟨1620846187573810255616467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2161128250098413674155289 1620846187573810255616467)
                  ·
                    refine ⟨2431269281360715383424701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1620846187573810255616467 2431269281360715383424701)
                    ·
                      refine ⟨911725980510268268784263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2431269281360715383424701 911725980510268268784263)
                      ·
                        rfl

theorem cell23_1775580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_1775580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1775580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1775580 prefixEnd_1775580 := by exact prefixLift 1775580
  have htrace : WordTrace (prefixWord ++ tailWord_1775580) baseStart_1775580 baseEnd_1775580 := by
    simpa [prefixWord, tailWord_1775580, baseEnd_1775580] using wordTrace_append hprefix tailTrace_1775580
  have hstable : (prefixWord ++ tailWord_1775580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775580).length < 2 ^ (prefixWord ++ tailWord_1775580).sum := by decide
  have hdescent : baseEnd_1775580 < baseStart_1775580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775612 : List Nat := [2, 2, 2, 1, 2, 2, 1, 2, 2, 5, 2]
def baseStart_1775612 : Nat := 118140960795 + 1775612 * 2 ^ 59
def prefixEnd_1775612 : Nat := 4983230072969 + 3 ^ 40 * 1775612 * 2
def baseEnd_1775612 : Nat := 911742411891212143584115

theorem tailTrace_1775612 : CollatzResearch.WordTrace tailWord_1775612 prefixEnd_1775612 911742411891212143584115 := by
  unfold tailWord_1775612
  simp only [CollatzResearch.WordTrace]
  refine ⟨32380945021634224615856545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43174593362178966154475393 32380945021634224615856545)
  ·
    refine ⟨24285708766225668461892409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32380945021634224615856545 24285708766225668461892409)
    ·
      refine ⟨18214281574669251346419307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24285708766225668461892409 18214281574669251346419307)
      ·
        refine ⟨27321422362003877019628961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18214281574669251346419307 27321422362003877019628961)
        ·
          refine ⟨20491066771502907764721721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27321422362003877019628961 20491066771502907764721721)
          ·
            refine ⟨15368300078627180823541291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20491066771502907764721721 15368300078627180823541291)
            ·
              refine ⟨23052450117940771235311937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15368300078627180823541291 23052450117940771235311937)
              ·
                refine ⟨17289337588455578426483953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23052450117940771235311937 17289337588455578426483953)
                ·
                  refine ⟨12967003191341683819862965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17289337588455578426483953 12967003191341683819862965)
                  ·
                    refine ⟨1215656549188282858112153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12967003191341683819862965 1215656549188282858112153)
                    ·
                      refine ⟨911742411891212143584115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1215656549188282858112153 911742411891212143584115)
                      ·
                        rfl

theorem cell23_1775612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 5, 2].length) (baseStart_1775612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1775612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1775612 prefixEnd_1775612 := by exact prefixLift 1775612
  have htrace : WordTrace (prefixWord ++ tailWord_1775612) baseStart_1775612 baseEnd_1775612 := by
    simpa [prefixWord, tailWord_1775612, baseEnd_1775612] using wordTrace_append hprefix tailTrace_1775612
  have hstable : (prefixWord ++ tailWord_1775612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775612).length < 2 ^ (prefixWord ++ tailWord_1775612).sum := by decide
  have hdescent : baseEnd_1775612 < baseStart_1775612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775719 : List Nat := [1, 1, 5, 1, 1, 2, 1, 2, 4, 3, 2]
def baseStart_1775719 : Nat := 118140960795 + 1775719 * 2 ^ 59
def prefixEnd_1775719 : Nat := 4983230072969 + 3 ^ 40 * 1775719 * 2
def baseEnd_1775719 : Nat := 911797354321243224946123

theorem tailTrace_1775719 : CollatzResearch.WordTrace tailWord_1775719 prefixEnd_1775719 911797354321243224946123 := by
  unfold tailWord_1775719
  simp only [CollatzResearch.WordTrace]
  refine ⟨64765792653880806505858211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43177195102587204337238807 64765792653880806505858211)
  ·
    refine ⟨97148688980821209758787317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64765792653880806505858211 97148688980821209758787317)
    ·
      refine ⟨9107689591951988414886311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97148688980821209758787317 9107689591951988414886311)
      ·
        refine ⟨13661534387927982622329467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9107689591951988414886311 13661534387927982622329467)
        ·
          refine ⟨20492301581891973933494201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13661534387927982622329467 20492301581891973933494201)
          ·
            refine ⟨15369226186418980450120651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20492301581891973933494201 15369226186418980450120651)
            ·
              refine ⟨23053839279628470675180977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15369226186418980450120651 23053839279628470675180977)
              ·
                refine ⟨17290379459721353006385733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23053839279628470675180977 17290379459721353006385733)
                ·
                  refine ⟨3241946148697753688697325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17290379459721353006385733 3241946148697753688697325)
                  ·
                    refine ⟨1215729805761657633261497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3241946148697753688697325 1215729805761657633261497)
                    ·
                      refine ⟨911797354321243224946123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1215729805761657633261497 911797354321243224946123)
                      ·
                        rfl

theorem cell23_1775719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 4, 3, 2].length) (baseStart_1775719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1775719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1775719 prefixEnd_1775719 := by exact prefixLift 1775719
  have htrace : WordTrace (prefixWord ++ tailWord_1775719) baseStart_1775719 baseEnd_1775719 := by
    simpa [prefixWord, tailWord_1775719, baseEnd_1775719] using wordTrace_append hprefix tailTrace_1775719
  have hstable : (prefixWord ++ tailWord_1775719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775719).length < 2 ^ (prefixWord ++ tailWord_1775719).sum := by decide
  have hdescent : baseEnd_1775719 < baseStart_1775719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775799 : List Nat := [1, 1, 3, 1, 4, 2, 2, 2, 1, 3, 3]
def baseStart_1775799 : Nat := 118140960795 + 1775799 * 2 ^ 59
def prefixEnd_1775799 : Nat := 4983230072969 + 3 ^ 40 * 1775799 * 2
def baseEnd_1775799 : Nat := 911838432773602911945755

theorem tailTrace_1775799 : CollatzResearch.WordTrace tailWord_1775799 prefixEnd_1775799 911838432773602911945755 := by
  unfold tailWord_1775799
  simp only [CollatzResearch.WordTrace]
  refine ⟨64768710493590980168770451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43179140329060653445846967 64768710493590980168770451)
  ·
    refine ⟨97153065740386470253155677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64768710493590980168770451 97153065740386470253155677)
    ·
      refine ⟨36432399652644926344933379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97153065740386470253155677 36432399652644926344933379)
      ·
        refine ⟨54648599478967389517400069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36432399652644926344933379 54648599478967389517400069)
        ·
          refine ⟨10246612402306385534512513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54648599478967389517400069 10246612402306385534512513)
          ·
            refine ⟨7684959301729789150884385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10246612402306385534512513 7684959301729789150884385)
            ·
              refine ⟨5763719476297341863163289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7684959301729789150884385 5763719476297341863163289)
              ·
                refine ⟨4322789607223006397372467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5763719476297341863163289 4322789607223006397372467)
                ·
                  refine ⟨6484184410834509596058701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4322789607223006397372467 6484184410834509596058701)
                  ·
                    refine ⟨2431569154062941098522013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6484184410834509596058701 2431569154062941098522013)
                    ·
                      refine ⟨911838432773602911945755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2431569154062941098522013 911838432773602911945755)
                      ·
                        rfl

theorem cell23_1775799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2, 1, 3, 3].length) (baseStart_1775799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1775799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1775799 prefixEnd_1775799 := by exact prefixLift 1775799
  have htrace : WordTrace (prefixWord ++ tailWord_1775799) baseStart_1775799 baseEnd_1775799 := by
    simpa [prefixWord, tailWord_1775799, baseEnd_1775799] using wordTrace_append hprefix tailTrace_1775799
  have hstable : (prefixWord ++ tailWord_1775799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775799).length < 2 ^ (prefixWord ++ tailWord_1775799).sum := by decide
  have hdescent : baseEnd_1775799 < baseStart_1775799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775810 : List Nat := [3, 5, 1, 1, 1, 1, 3, 2, 2, 4]
def baseStart_1775810 : Nat := 118140960795 + 1775810 * 2 ^ 59
def prefixEnd_1775810 : Nat := 4983230072969 + 3 ^ 40 * 1775810 * 2
def baseEnd_1775810 : Nat := 303948027020267456302735

theorem tailTrace_1775810 : CollatzResearch.WordTrace tailWord_1775810 prefixEnd_1775810 303948027020267456302735 := by
  unfold tailWord_1775810
  simp only [CollatzResearch.WordTrace]
  refine ⟨16192277924137782261855221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43179407797700752698280589 16192277924137782261855221)
  ·
    refine ⟨1518026055387917087048927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16192277924137782261855221 1518026055387917087048927)
    ·
      refine ⟨2277039083081875630573391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1518026055387917087048927 2277039083081875630573391)
      ·
        refine ⟨3415558624622813445860087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2277039083081875630573391 3415558624622813445860087)
        ·
          refine ⟨5123337936934220168790131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3415558624622813445860087 5123337936934220168790131)
          ·
            refine ⟨7685006905401330253185197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5123337936934220168790131 7685006905401330253185197)
            ·
              refine ⟨2881877589525498844944449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7685006905401330253185197 2881877589525498844944449)
              ·
                refine ⟨2161408192144124133708337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2881877589525498844944449 2161408192144124133708337)
                ·
                  refine ⟨1621056144108093100281253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2161408192144124133708337 1621056144108093100281253)
                  ·
                    refine ⟨303948027020267456302735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1621056144108093100281253 303948027020267456302735)
                    ·
                      rfl

theorem cell23_1775810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_1775810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1775810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1775810 prefixEnd_1775810 := by exact prefixLift 1775810
  have htrace : WordTrace (prefixWord ++ tailWord_1775810) baseStart_1775810 baseEnd_1775810 := by
    simpa [prefixWord, tailWord_1775810, baseEnd_1775810] using wordTrace_append hprefix tailTrace_1775810
  have hstable : (prefixWord ++ tailWord_1775810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775810).length < 2 ^ (prefixWord ++ tailWord_1775810).sum := by decide
  have hdescent : baseEnd_1775810 < baseStart_1775810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775873 : List Nat := [1, 2, 4, 1, 1, 2, 2, 4, 2, 2, 2]
def baseStart_1775873 : Nat := 118140960795 + 1775873 * 2 ^ 59
def prefixEnd_1775873 : Nat := 4983230072969 + 3 ^ 40 * 1775873 * 2
def baseEnd_1775873 : Nat := 911876430342035622420415

theorem tailTrace_1775873 : CollatzResearch.WordTrace tailWord_1775873 prefixEnd_1775873 911876430342035622420415 := by
  unfold tailWord_1775873
  simp only [CollatzResearch.WordTrace]
  refine ⟨64771409495322890806964273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43180939663548593871309515 64771409495322890806964273)
  ·
    refine ⟨48578557121492168105223205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64771409495322890806964273 48578557121492168105223205)
    ·
      refine ⟨9108479460279781519729351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48578557121492168105223205 9108479460279781519729351)
      ·
        refine ⟨13662719190419672279594027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9108479460279781519729351 13662719190419672279594027)
        ·
          refine ⟨20494078785629508419391041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13662719190419672279594027 20494078785629508419391041)
          ·
            refine ⟨15370559089222131314543281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20494078785629508419391041 15370559089222131314543281)
            ·
              refine ⟨11527919316916598485907461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15370559089222131314543281 11527919316916598485907461)
              ·
                refine ⟨2161484871921862216107649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11527919316916598485907461 2161484871921862216107649)
                ·
                  refine ⟨1621113653941396662080737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2161484871921862216107649 1621113653941396662080737)
                  ·
                    refine ⟨1215835240456047496560553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1621113653941396662080737 1215835240456047496560553)
                    ·
                      refine ⟨911876430342035622420415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1215835240456047496560553 911876430342035622420415)
                      ·
                        rfl

theorem cell23_1775873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 4, 2, 2, 2].length) (baseStart_1775873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1775873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1775873 prefixEnd_1775873 := by exact prefixLift 1775873
  have htrace : WordTrace (prefixWord ++ tailWord_1775873) baseStart_1775873 baseEnd_1775873 := by
    simpa [prefixWord, tailWord_1775873, baseEnd_1775873] using wordTrace_append hprefix tailTrace_1775873
  have hstable : (prefixWord ++ tailWord_1775873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775873).length < 2 ^ (prefixWord ++ tailWord_1775873).sum := by decide
  have hdescent : baseEnd_1775873 < baseStart_1775873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775956 : List Nat := [2, 4, 1, 1, 2, 2, 1, 1, 5, 4]
def baseStart_1775956 : Nat := 118140960795 + 1775956 * 2 ^ 59
def prefixEnd_1775956 : Nat := 4983230072969 + 3 ^ 40 * 1775956 * 2
def baseEnd_1775956 : Nat := 303973016412119599227511

theorem tailTrace_1775956 : CollatzResearch.WordTrace tailWord_1775956 prefixEnd_1775956 303973016412119599227511 := by
  unfold tailWord_1775956
  simp only [CollatzResearch.WordTrace]
  refine ⟨32387218377011097991117861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43182957836014797321490481 32387218377011097991117861)
  ·
    refine ⟨6072603445689580873334599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32387218377011097991117861 6072603445689580873334599)
    ·
      refine ⟨9108905168534371310001899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6072603445689580873334599 9108905168534371310001899)
      ·
        refine ⟨13663357752801556965002849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9108905168534371310001899 13663357752801556965002849)
        ·
          refine ⟨10247518314601167723752137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13663357752801556965002849 10247518314601167723752137)
          ·
            refine ⟨7685638735950875792814103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10247518314601167723752137 7685638735950875792814103)
            ·
              refine ⟨11528458103926313689221155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7685638735950875792814103 11528458103926313689221155)
              ·
                refine ⟨17292687155889470533831733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11528458103926313689221155 17292687155889470533831733)
                ·
                  refine ⟨1621189420864637862546725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17292687155889470533831733 1621189420864637862546725)
                  ·
                    refine ⟨303973016412119599227511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1621189420864637862546725 303973016412119599227511)
                    ·
                      rfl

theorem cell23_1775956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_1775956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1775956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1775956 prefixEnd_1775956 := by exact prefixLift 1775956
  have htrace : WordTrace (prefixWord ++ tailWord_1775956) baseStart_1775956 baseEnd_1775956 := by
    simpa [prefixWord, tailWord_1775956, baseEnd_1775956] using wordTrace_append hprefix tailTrace_1775956
  have hstable : (prefixWord ++ tailWord_1775956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775956).length < 2 ^ (prefixWord ++ tailWord_1775956).sum := by decide
  have hdescent : baseEnd_1775956 < baseStart_1775956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775973 : List Nat := [1, 3, 1, 3, 1, 3, 1, 5, 1, 4]
def baseStart_1775973 : Nat := 118140960795 + 1775973 * 2 ^ 59
def prefixEnd_1775973 : Nat := 4983230072969 + 3 ^ 40 * 1775973 * 2
def baseEnd_1775973 : Nat := 303975926135828410389985

theorem tailTrace_1775973 : CollatzResearch.WordTrace tailWord_1775973 prefixEnd_1775973 303975926135828410389985 := by
  unfold tailWord_1775973
  simp only [CollatzResearch.WordTrace]
  refine ⟨64775056794960607885604573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43183371196640405257069715 64775056794960607885604573)
  ·
    refine ⟨24290646298110227957101715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64775056794960607885604573 24290646298110227957101715)
    ·
      refine ⟨36435969447165341935652573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24290646298110227957101715 36435969447165341935652573)
      ·
        refine ⟨13663488542687003225869715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36435969447165341935652573 13663488542687003225869715)
        ·
          refine ⟨20495232814030504838804573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13663488542687003225869715 20495232814030504838804573)
          ·
            refine ⟨7685712305261439314551715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20495232814030504838804573 7685712305261439314551715)
            ·
              refine ⟨11528568457892158971827573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7685712305261439314551715 11528568457892158971827573)
              ·
                refine ⟨1080803292927389903608835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11528568457892158971827573 1080803292927389903608835)
                ·
                  refine ⟨1621204939391084855413253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1080803292927389903608835 1621204939391084855413253)
                  ·
                    refine ⟨303975926135828410389985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1621204939391084855413253 303975926135828410389985)
                    ·
                      rfl

theorem cell23_1775973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 5, 1, 4].length) (baseStart_1775973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1775973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1775973 prefixEnd_1775973 := by exact prefixLift 1775973
  have htrace : WordTrace (prefixWord ++ tailWord_1775973) baseStart_1775973 baseEnd_1775973 := by
    simpa [prefixWord, tailWord_1775973, baseEnd_1775973] using wordTrace_append hprefix tailTrace_1775973
  have hstable : (prefixWord ++ tailWord_1775973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775973).length < 2 ^ (prefixWord ++ tailWord_1775973).sum := by decide
  have hdescent : baseEnd_1775973 < baseStart_1775973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1775986 : List Nat := [3, 2, 1, 2, 1, 3, 3, 2, 6]
def baseStart_1775986 : Nat := 118140960795 + 1775986 * 2 ^ 59
def prefixEnd_1775986 : Nat := 4983230072969 + 3 ^ 40 * 1775986 * 2
def baseEnd_1775986 : Nat := 101326050406221520034155

theorem tailTrace_1775986 : CollatzResearch.WordTrace tailWord_1775986 prefixEnd_1775986 101326050406221520034155 := by
  unfold tailWord_1775986
  simp only [CollatzResearch.WordTrace]
  refine ⟨16193882735978377776456953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43183687295942340737218541 16193882735978377776456953)
  ·
    refine ⟨12145412051983783332342715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16193882735978377776456953 12145412051983783332342715)
    ·
      refine ⟨18218118077975674998514073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12145412051983783332342715 18218118077975674998514073)
      ·
        refine ⟨13663588558481756248885555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18218118077975674998514073 13663588558481756248885555)
        ·
          refine ⟨20495382837722634373328333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13663588558481756248885555 20495382837722634373328333)
          ·
            refine ⟨7685768564145987889998125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20495382837722634373328333 7685768564145987889998125)
            ·
              refine ⟨2882163211554745458749297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7685768564145987889998125 2882163211554745458749297)
              ·
                refine ⟨2161622408666059094061973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2882163211554745458749297 2161622408666059094061973)
                ·
                  refine ⟨101326050406221520034155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2161622408666059094061973 101326050406221520034155)
                  ·
                    rfl

theorem cell23_1775986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 2, 6].length) (baseStart_1775986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1775986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1775986 prefixEnd_1775986 := by exact prefixLift 1775986
  have htrace : WordTrace (prefixWord ++ tailWord_1775986) baseStart_1775986 baseEnd_1775986 := by
    simpa [prefixWord, tailWord_1775986, baseEnd_1775986] using wordTrace_append hprefix tailTrace_1775986
  have hstable : (prefixWord ++ tailWord_1775986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1775986).length < 2 ^ (prefixWord ++ tailWord_1775986).sum := by decide
  have hdescent : baseEnd_1775986 < baseStart_1775986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1775986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776003 : List Nat := [1, 1, 1, 3, 6, 1, 3, 1, 6]
def baseStart_1776003 : Nat := 118140960795 + 1776003 * 2 ^ 59
def prefixEnd_1776003 : Nat := 4983230072969 + 3 ^ 40 * 1776003 * 2
def baseEnd_1776003 : Nat := 101327020314124457088313

theorem tailTrace_1776003 : CollatzResearch.WordTrace tailWord_1776003 prefixEnd_1776003 101327020314124457088313 := by
  unfold tailWord_1776003
  simp only [CollatzResearch.WordTrace]
  refine ⟨64776150984851923009196663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43184100656567948672797775 64776150984851923009196663)
  ·
    refine ⟨97164226477277884513794995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64776150984851923009196663 97164226477277884513794995)
    ·
      refine ⟨145746339715916826770692493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97164226477277884513794995 145746339715916826770692493)
      ·
        refine ⟨54654877393468810039009685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145746339715916826770692493 54654877393468810039009685)
        ·
          refine ⟨2561947377818850470578579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 54654877393468810039009685 2561947377818850470578579)
          ·
            refine ⟨3842921066728275705867869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2561947377818850470578579 3842921066728275705867869)
            ·
              refine ⟨1441095400023103389700451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3842921066728275705867869 1441095400023103389700451)
              ·
                refine ⟨2161643100034655084550677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1441095400023103389700451 2161643100034655084550677)
                ·
                  refine ⟨101327020314124457088313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2161643100034655084550677 101327020314124457088313)
                  ·
                    rfl

theorem cell23_1776003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 1, 6].length) (baseStart_1776003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1776003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1776003 prefixEnd_1776003 := by exact prefixLift 1776003
  have htrace : WordTrace (prefixWord ++ tailWord_1776003) baseStart_1776003 baseEnd_1776003 := by
    simpa [prefixWord, tailWord_1776003, baseEnd_1776003] using wordTrace_append hprefix tailTrace_1776003
  have hstable : (prefixWord ++ tailWord_1776003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776003).length < 2 ^ (prefixWord ++ tailWord_1776003).sum := by decide
  have hdescent : baseEnd_1776003 < baseStart_1776003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776040 : List Nat := [2, 1, 6, 1, 1, 1, 1, 1, 4, 3, 2]
def baseStart_1776040 : Nat := 118140960795 + 1776040 * 2 ^ 59
def prefixEnd_1776040 : Nat := 4983230072969 + 3 ^ 40 * 1776040 * 2
def baseEnd_1776040 : Nat := 911962181611336469032147

theorem tailTrace_1776040 : CollatzResearch.WordTrace tailWord_1776040 prefixEnd_1776040 911962181611336469032147 := by
  unfold tailWord_1776040
  simp only [CollatzResearch.WordTrace]
  refine ⟨32388750242858939164146787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43185000323811918885529049 32388750242858939164146787)
  ·
    refine ⟨48583125364288408746220181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32388750242858939164146787 48583125364288408746220181)
    ·
      refine ⟨2277334001451019159979071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 48583125364288408746220181 2277334001451019159979071)
      ·
        refine ⟨3416001002176528739968607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2277334001451019159979071 3416001002176528739968607)
        ·
          refine ⟨5124001503264793109952911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3416001002176528739968607 5124001503264793109952911)
          ·
            refine ⟨7686002254897189664929367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5124001503264793109952911 7686002254897189664929367)
            ·
              refine ⟨11529003382345784497394051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7686002254897189664929367 11529003382345784497394051)
              ·
                refine ⟨17293505073518676746091077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11529003382345784497394051 17293505073518676746091077)
                ·
                  refine ⟨3242532201284751889892077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17293505073518676746091077 3242532201284751889892077)
                  ·
                    refine ⟨1215949575481781958709529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3242532201284751889892077 1215949575481781958709529)
                    ·
                      refine ⟨911962181611336469032147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1215949575481781958709529 911962181611336469032147)
                      ·
                        rfl

theorem cell23_1776040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_1776040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1776040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1776040 prefixEnd_1776040 := by exact prefixLift 1776040
  have htrace : WordTrace (prefixWord ++ tailWord_1776040) baseStart_1776040 baseEnd_1776040 := by
    simpa [prefixWord, tailWord_1776040, baseEnd_1776040] using wordTrace_append hprefix tailTrace_1776040
  have hstable : (prefixWord ++ tailWord_1776040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776040).length < 2 ^ (prefixWord ++ tailWord_1776040).sum := by decide
  have hdescent : baseEnd_1776040 < baseStart_1776040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776056 : List Nat := [2, 1, 2, 1, 2, 2, 1, 4, 3, 2, 3]
def baseStart_1776056 : Nat := 118140960795 + 1776056 * 2 ^ 59
def prefixEnd_1776056 : Nat := 4983230072969 + 3 ^ 40 * 1776056 * 2
def baseEnd_1776056 : Nat := 911970397301808406432073

theorem tailTrace_1776056 : CollatzResearch.WordTrace tailWord_1776056 prefixEnd_1776056 911970397301808406432073 := by
  unfold tailWord_1776056
  simp only [CollatzResearch.WordTrace]
  refine ⟨32389042026829956530438011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43185389369106608707250681 32389042026829956530438011)
  ·
    refine ⟨48583563040244934795657017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32389042026829956530438011 48583563040244934795657017)
    ·
      refine ⟨36437672280183701096742763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48583563040244934795657017 36437672280183701096742763)
      ·
        refine ⟨54656508420275551645114145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36437672280183701096742763 54656508420275551645114145)
        ·
          refine ⟨40992381315206663733835609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54656508420275551645114145 40992381315206663733835609)
          ·
            refine ⟨30744285986404997800376707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40992381315206663733835609 30744285986404997800376707)
            ·
              refine ⟨46116428979607496700565061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30744285986404997800376707 46116428979607496700565061)
              ·
                refine ⟨8646830433676405631355949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46116428979607496700565061 8646830433676405631355949)
                ·
                  refine ⟨3242561412628652111758481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8646830433676405631355949 3242561412628652111758481)
                  ·
                    refine ⟨2431921059471489083818861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3242561412628652111758481 2431921059471489083818861)
                    ·
                      refine ⟨911970397301808406432073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2431921059471489083818861 911970397301808406432073)
                      ·
                        rfl

theorem cell23_1776056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 3, 2, 3].length) (baseStart_1776056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1776056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1776056 prefixEnd_1776056 := by exact prefixLift 1776056
  have htrace : WordTrace (prefixWord ++ tailWord_1776056) baseStart_1776056 baseEnd_1776056 := by
    simpa [prefixWord, tailWord_1776056, baseEnd_1776056] using wordTrace_append hprefix tailTrace_1776056
  have hstable : (prefixWord ++ tailWord_1776056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776056).length < 2 ^ (prefixWord ++ tailWord_1776056).sum := by decide
  have hdescent : baseEnd_1776056 < baseStart_1776056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776073 : List Nat := [1, 2, 1, 1, 2, 1, 7, 2, 1, 2, 3]
def baseStart_1776073 : Nat := 118140960795 + 1776073 * 2 ^ 59
def prefixEnd_1776073 : Nat := 4983230072969 + 3 ^ 40 * 1776073 * 2
def baseEnd_1776073 : Nat := 911979126472934839919495

theorem tailTrace_1776073 : CollatzResearch.WordTrace tailWord_1776073 prefixEnd_1776073 911979126472934839919495 := by
  unfold tailWord_1776073
  simp only [CollatzResearch.WordTrace]
  refine ⟨64778704094598324964244873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43185802729732216642829915 64778704094598324964244873)
  ·
    refine ⟨48584028070948743723183655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64778704094598324964244873 48584028070948743723183655)
    ·
      refine ⟨72876042106423115584775483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48584028070948743723183655 72876042106423115584775483)
      ·
        refine ⟨109314063159634673377163225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72876042106423115584775483 109314063159634673377163225)
        ·
          refine ⟨81985547369726005032872419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109314063159634673377163225 81985547369726005032872419)
          ·
            refine ⟨122978321054589007549308629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81985547369726005032872419 122978321054589007549308629)
            ·
              refine ⟨2882304399716929864436921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 122978321054589007549308629 2882304399716929864436921)
              ·
                refine ⟨2161728299787697398327691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2882304399716929864436921 2161728299787697398327691)
                ·
                  refine ⟨3242592449681546097491537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2161728299787697398327691 3242592449681546097491537)
                  ·
                    refine ⟨2431944337261159573118653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3242592449681546097491537 2431944337261159573118653)
                    ·
                      refine ⟨911979126472934839919495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2431944337261159573118653 911979126472934839919495)
                      ·
                        rfl

theorem cell23_1776073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 2, 1, 2, 3].length) (baseStart_1776073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1776073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1776073 prefixEnd_1776073 := by exact prefixLift 1776073
  have htrace : WordTrace (prefixWord ++ tailWord_1776073) baseStart_1776073 baseEnd_1776073 := by
    simpa [prefixWord, tailWord_1776073, baseEnd_1776073] using wordTrace_append hprefix tailTrace_1776073
  have hstable : (prefixWord ++ tailWord_1776073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776073).length < 2 ^ (prefixWord ++ tailWord_1776073).sum := by decide
  have hdescent : baseEnd_1776073 < baseStart_1776073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776090 : List Nat := [3, 1, 1, 2, 3, 1, 5, 1, 1, 2, 3]
def baseStart_1776090 : Nat := 118140960795 + 1776090 * 2 ^ 59
def prefixEnd_1776090 : Nat := 4983230072969 + 3 ^ 40 * 1776090 * 2
def baseEnd_1776090 : Nat := 911987855644061273406917

theorem tailTrace_1776090 : CollatzResearch.WordTrace tailWord_1776090 prefixEnd_1776090 911987855644061273406917 := by
  unfold tailWord_1776090
  simp only [CollatzResearch.WordTrace]
  refine ⟨16194831033884184216903431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43186216090357824578409149 16194831033884184216903431)
  ·
    refine ⟨24292246550826276325355147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16194831033884184216903431 24292246550826276325355147)
    ·
      refine ⟨36438369826239414488032721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24292246550826276325355147 36438369826239414488032721)
      ·
        refine ⟨27328777369679560866024541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36438369826239414488032721 27328777369679560866024541)
        ·
          refine ⟨10248291513629835324759203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27328777369679560866024541 10248291513629835324759203)
          ·
            refine ⟨15372437270444752987138805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10248291513629835324759203 15372437270444752987138805)
            ·
              refine ⟨1441165994104195592544263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15372437270444752987138805 1441165994104195592544263)
              ·
                refine ⟨2161748991156293388816395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1441165994104195592544263 2161748991156293388816395)
                ·
                  refine ⟨3242623486734440083224593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2161748991156293388816395 3242623486734440083224593)
                  ·
                    refine ⟨2431967615050830062418445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3242623486734440083224593 2431967615050830062418445)
                    ·
                      refine ⟨911987855644061273406917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2431967615050830062418445 911987855644061273406917)
                      ·
                        rfl

theorem cell23_1776090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 1, 1, 2, 3].length) (baseStart_1776090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1776090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1776090 prefixEnd_1776090 := by exact prefixLift 1776090
  have htrace : WordTrace (prefixWord ++ tailWord_1776090) baseStart_1776090 baseEnd_1776090 := by
    simpa [prefixWord, tailWord_1776090, baseEnd_1776090] using wordTrace_append hprefix tailTrace_1776090
  have hstable : (prefixWord ++ tailWord_1776090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776090).length < 2 ^ (prefixWord ++ tailWord_1776090).sum := by decide
  have hdescent : baseEnd_1776090 < baseStart_1776090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776098 : List Nat := [3, 3, 3, 2, 1, 2, 2, 2, 1, 1, 3]
def baseStart_1776098 : Nat := 118140960795 + 1776098 * 2 ^ 59
def prefixEnd_1776098 : Nat := 4983230072969 + 3 ^ 40 * 1776098 * 2
def baseEnd_1776098 : Nat := 911991963489297242106881

theorem tailTrace_1776098 : CollatzResearch.WordTrace tailWord_1776098 prefixEnd_1776098 911991963489297242106881 := by
  unfold tailWord_1776098
  simp only [CollatzResearch.WordTrace]
  refine ⟨16194903979876938558476237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43186410613005169489269965 16194903979876938558476237)
  ·
    refine ⟨6073088992453851959428589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16194903979876938558476237 6073088992453851959428589)
    ·
      refine ⟨2277408372170194484785721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6073088992453851959428589 2277408372170194484785721)
      ·
        refine ⟨1708056279127645863589291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2277408372170194484785721 1708056279127645863589291)
        ·
          refine ⟨2562084418691468795383937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1708056279127645863589291 2562084418691468795383937)
          ·
            refine ⟨1921563314018601596537953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2562084418691468795383937 1921563314018601596537953)
            ·
              refine ⟨1441172485513951197403465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1921563314018601596537953 1441172485513951197403465)
              ·
                refine ⟨1080879364135463398052599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1441172485513951197403465 1080879364135463398052599)
                ·
                  refine ⟨1621319046203195097078899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1080879364135463398052599 1621319046203195097078899)
                  ·
                    refine ⟨2431978569304792645618349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1621319046203195097078899 2431978569304792645618349)
                    ·
                      refine ⟨911991963489297242106881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2431978569304792645618349 911991963489297242106881)
                      ·
                        rfl

theorem cell23_1776098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_1776098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1776098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1776098 prefixEnd_1776098 := by exact prefixLift 1776098
  have htrace : WordTrace (prefixWord ++ tailWord_1776098) baseStart_1776098 baseEnd_1776098 := by
    simpa [prefixWord, tailWord_1776098, baseEnd_1776098] using wordTrace_append hprefix tailTrace_1776098
  have hstable : (prefixWord ++ tailWord_1776098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776098).length < 2 ^ (prefixWord ++ tailWord_1776098).sum := by decide
  have hdescent : baseEnd_1776098 < baseStart_1776098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776104 : List Nat := [2, 1, 4, 1, 1, 3, 4, 2, 1, 2, 2]
def baseStart_1776104 : Nat := 118140960795 + 1776104 * 2 ^ 59
def prefixEnd_1776104 : Nat := 4983230072969 + 3 ^ 40 * 1776104 * 2
def baseEnd_1776104 : Nat := 911995044373224218631853

theorem tailTrace_1776104 : CollatzResearch.WordTrace tailWord_1776104 prefixEnd_1776104 911995044373224218631853 := by
  unfold tailWord_1776104
  simp only [CollatzResearch.WordTrace]
  refine ⟨32389917378743008629311683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43186556504990678172415577 32389917378743008629311683)
  ·
    refine ⟨48584876068114512943967525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32389917378743008629311683 48584876068114512943967525)
    ·
      refine ⟨9109664262771471176993911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48584876068114512943967525 9109664262771471176993911)
      ·
        refine ⟨13664496394157206765490867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9109664262771471176993911 13664496394157206765490867)
        ·
          refine ⟨20496744591235810148236301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13664496394157206765490867 20496744591235810148236301)
          ·
            refine ⟨7686279221713428805588613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20496744591235810148236301 7686279221713428805588613)
            ·
              refine ⟨1441177354071267901047865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7686279221713428805588613 1441177354071267901047865)
              ·
                refine ⟨1080883015553450925785899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1441177354071267901047865 1080883015553450925785899)
                ·
                  refine ⟨1621324523330176388678849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1080883015553450925785899 1621324523330176388678849)
                  ·
                    refine ⟨1215993392497632291509137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1621324523330176388678849 1215993392497632291509137)
                    ·
                      refine ⟨911995044373224218631853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1215993392497632291509137 911995044373224218631853)
                      ·
                        rfl

theorem cell23_1776104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 2, 1, 2, 2].length) (baseStart_1776104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1776104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1776104 prefixEnd_1776104 := by exact prefixLift 1776104
  have htrace : WordTrace (prefixWord ++ tailWord_1776104) baseStart_1776104 baseEnd_1776104 := by
    simpa [prefixWord, tailWord_1776104, baseEnd_1776104] using wordTrace_append hprefix tailTrace_1776104
  have hstable : (prefixWord ++ tailWord_1776104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776104).length < 2 ^ (prefixWord ++ tailWord_1776104).sum := by decide
  have hdescent : baseEnd_1776104 < baseStart_1776104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776106 : List Nat := [3, 1, 3, 1, 3, 1, 1, 1, 2, 7]
def baseStart_1776106 : Nat := 118140960795 + 1776106 * 2 ^ 59
def prefixEnd_1776106 : Nat := 4983230072969 + 3 ^ 40 * 1776106 * 2
def baseEnd_1776106 : Nat := 303998690444844403602281

theorem tailTrace_1776106 : CollatzResearch.WordTrace tailWord_1776106 prefixEnd_1776106 303998690444844403602281 := by
  unfold tailWord_1776106
  simp only [CollatzResearch.WordTrace]
  refine ⟨16194976925869692900049043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43186605135652514400130781 16194976925869692900049043)
  ·
    refine ⟨24292465388804539350073565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16194976925869692900049043 24292465388804539350073565)
    ·
      refine ⟨9109674520801702256277587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24292465388804539350073565 9109674520801702256277587)
      ·
        refine ⟨13664511781202553384416381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9109674520801702256277587 13664511781202553384416381)
        ·
          refine ⟨5124191917950957519156143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13664511781202553384416381 5124191917950957519156143)
          ·
            refine ⟨7686287876926436278734215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5124191917950957519156143 7686287876926436278734215)
            ·
              refine ⟨11529431815389654418101323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7686287876926436278734215 11529431815389654418101323)
              ·
                refine ⟨17294147723084481627151985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11529431815389654418101323 17294147723084481627151985)
                ·
                  refine ⟨12970610792313361220363989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17294147723084481627151985 12970610792313361220363989)
                  ·
                    refine ⟨303998690444844403602281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12970610792313361220363989 303998690444844403602281)
                    ·
                      rfl

theorem cell23_1776106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_1776106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1776106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1776106 prefixEnd_1776106 := by exact prefixLift 1776106
  have htrace : WordTrace (prefixWord ++ tailWord_1776106) baseStart_1776106 baseEnd_1776106 := by
    simpa [prefixWord, tailWord_1776106, baseEnd_1776106] using wordTrace_append hprefix tailTrace_1776106
  have hstable : (prefixWord ++ tailWord_1776106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776106).length < 2 ^ (prefixWord ++ tailWord_1776106).sum := by decide
  have hdescent : baseEnd_1776106 < baseStart_1776106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776113 : List Nat := [1, 2, 2, 2, 3, 1, 1, 1, 5, 3, 2]
def baseStart_1776113 : Nat := 118140960795 + 1776113 * 2 ^ 59
def prefixEnd_1776113 : Nat := 4983230072969 + 3 ^ 40 * 1776113 * 2
def baseEnd_1776113 : Nat := 911999665699114683419311

theorem tailTrace_1776113 : CollatzResearch.WordTrace tailWord_1776113 prefixEnd_1776113 911999665699114683419311 := by
  unfold tailWord_1776113
  simp only [CollatzResearch.WordTrace]
  refine ⟨64780163014453411795700993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43186775342968941197133995 64780163014453411795700993)
  ·
    refine ⟨48585122260840058846775745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64780163014453411795700993 48585122260840058846775745)
    ·
      refine ⟨36438841695630044135081809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48585122260840058846775745 36438841695630044135081809)
      ·
        refine ⟨27329131271722533101311357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36438841695630044135081809 27329131271722533101311357)
        ·
          refine ⟨10248424226895949912991759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27329131271722533101311357 10248424226895949912991759)
          ·
            refine ⟨15372636340343924869487639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10248424226895949912991759 15372636340343924869487639)
            ·
              refine ⟨23058954510515887304231459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15372636340343924869487639 23058954510515887304231459)
              ·
                refine ⟨34588431765773830956347189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23058954510515887304231459 34588431765773830956347189)
                ·
                  refine ⟨3242665478041296652157549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34588431765773830956347189 3242665478041296652157549)
                  ·
                    refine ⟨1215999554265486244559081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3242665478041296652157549 1215999554265486244559081)
                    ·
                      refine ⟨911999665699114683419311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1215999554265486244559081 911999665699114683419311)
                      ·
                        rfl

theorem cell23_1776113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 5, 3, 2].length) (baseStart_1776113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1776113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1776113 prefixEnd_1776113 := by exact prefixLift 1776113
  have htrace : WordTrace (prefixWord ++ tailWord_1776113) baseStart_1776113 baseEnd_1776113 := by
    simpa [prefixWord, tailWord_1776113, baseEnd_1776113] using wordTrace_append hprefix tailTrace_1776113
  have hstable : (prefixWord ++ tailWord_1776113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776113).length < 2 ^ (prefixWord ++ tailWord_1776113).sum := by decide
  have hdescent : baseEnd_1776113 < baseStart_1776113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776141 : List Nat := [1, 7, 1, 1, 1, 3, 2, 1, 1, 2, 3]
def baseStart_1776141 : Nat := 118140960795 + 1776141 * 2 ^ 59
def prefixEnd_1776141 : Nat := 4983230072969 + 3 ^ 40 * 1776141 * 2
def baseEnd_1776141 : Nat := 912014043157440573869183

theorem tailTrace_1776141 : CollatzResearch.WordTrace tailWord_1776141 prefixEnd_1776141 912014043157440573869183 := by
  unfold tailWord_1776141
  simp only [CollatzResearch.WordTrace]
  refine ⟨64781184258351972577720277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43187456172234648385146851 64781184258351972577720277)
  ·
    refine ⟨1518309006055124357290319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 64781184258351972577720277 1518309006055124357290319)
    ·
      refine ⟨2277463509082686535935479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1518309006055124357290319 2277463509082686535935479)
      ·
        refine ⟨3416195263624029803903219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2277463509082686535935479 3416195263624029803903219)
        ·
          refine ⟨5124292895436044705854829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3416195263624029803903219 5124292895436044705854829)
          ·
            refine ⟨1921609835788516764695561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5124292895436044705854829 1921609835788516764695561)
            ·
              refine ⟨1441207376841387573521671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1921609835788516764695561 1441207376841387573521671)
              ·
                refine ⟨2161811065262081360282507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1441207376841387573521671 2161811065262081360282507)
                ·
                  refine ⟨3242716597893122040423761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2161811065262081360282507 3242716597893122040423761)
                  ·
                    refine ⟨2432037448419841530317821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3242716597893122040423761 2432037448419841530317821)
                    ·
                      refine ⟨912014043157440573869183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2432037448419841530317821 912014043157440573869183)
                      ·
                        rfl

theorem cell23_1776141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_1776141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1776141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1776141 prefixEnd_1776141 := by exact prefixLift 1776141
  have htrace : WordTrace (prefixWord ++ tailWord_1776141) baseStart_1776141 baseEnd_1776141 := by
    simpa [prefixWord, tailWord_1776141, baseEnd_1776141] using wordTrace_append hprefix tailTrace_1776141
  have hstable : (prefixWord ++ tailWord_1776141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776141).length < 2 ^ (prefixWord ++ tailWord_1776141).sum := by decide
  have hdescent : baseEnd_1776141 < baseStart_1776141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776233 : List Nat := [1, 2, 1, 1, 1, 4, 1, 3, 1, 6, 2]
def baseStart_1776233 : Nat := 118140960795 + 1776233 * 2 ^ 59
def prefixEnd_1776233 : Nat := 4983230072969 + 3 ^ 40 * 1776233 * 2
def baseEnd_1776233 : Nat := 912061283377654213918759

theorem tailTrace_1776233 : CollatzResearch.WordTrace tailWord_1776233 prefixEnd_1776233 912061283377654213918759 := by
  unfold tailWord_1776233
  simp only [CollatzResearch.WordTrace]
  refine ⟨64784539774018672290069353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43189693182679114860046235 64784539774018672290069353)
  ·
    refine ⟨48588404830514004217552015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64784539774018672290069353 48588404830514004217552015)
    ·
      refine ⟨72882607245771006326328023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48588404830514004217552015 72882607245771006326328023)
      ·
        refine ⟨109323910868656509489492035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72882607245771006326328023 109323910868656509489492035)
        ·
          refine ⟨163985866302984764234238053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109323910868656509489492035 163985866302984764234238053)
          ·
            refine ⟨30747349931809643293919635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 163985866302984764234238053 30747349931809643293919635)
            ·
              refine ⟨46121024897714464940879453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30747349931809643293919635 46121024897714464940879453)
              ·
                refine ⟨17295384336642924352829795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46121024897714464940879453 17295384336642924352829795)
                ·
                  refine ⟨25943076504964386529244693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17295384336642924352829795 25943076504964386529244693)
                  ·
                    refine ⟨1216081711170205618558345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25943076504964386529244693 1216081711170205618558345)
                    ·
                      refine ⟨912061283377654213918759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1216081711170205618558345 912061283377654213918759)
                      ·
                        rfl

theorem cell23_1776233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 6, 2].length) (baseStart_1776233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1776233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1776233 prefixEnd_1776233 := by exact prefixLift 1776233
  have htrace : WordTrace (prefixWord ++ tailWord_1776233) baseStart_1776233 baseEnd_1776233 := by
    simpa [prefixWord, tailWord_1776233, baseEnd_1776233] using wordTrace_append hprefix tailTrace_1776233
  have hstable : (prefixWord ++ tailWord_1776233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776233).length < 2 ^ (prefixWord ++ tailWord_1776233).sum := by decide
  have hdescent : baseEnd_1776233 < baseStart_1776233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776270 : List Nat := [4, 1, 1, 3, 1, 1, 1, 4, 2, 2, 3]
def baseStart_1776270 : Nat := 118140960795 + 1776270 * 2 ^ 59
def prefixEnd_1776270 : Nat := 4983230072969 + 3 ^ 40 * 1776270 * 2
def baseEnd_1776270 : Nat := 912080282161870569156089

theorem tailTrace_1776270 : CollatzResearch.WordTrace tailWord_1776270 prefixEnd_1776270 912080282161870569156089 := by
  unfold tailWord_1776270
  simp only [CollatzResearch.WordTrace]
  refine ⟨8098236159360578451145783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43190592849923085072777509 8098236159360578451145783)
  ·
    refine ⟨12147354239040867676718675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8098236159360578451145783 12147354239040867676718675)
    ·
      refine ⟨18221031358561301515078013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12147354239040867676718675 18221031358561301515078013)
      ·
        refine ⟨6832886759460488068154255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18221031358561301515078013 6832886759460488068154255)
        ·
          refine ⟨10249330139190732102231383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6832886759460488068154255 10249330139190732102231383)
          ·
            refine ⟨15373995208786098153347075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10249330139190732102231383 15373995208786098153347075)
            ·
              refine ⟨23060992813179147230020613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15373995208786098153347075 23060992813179147230020613)
              ·
                refine ⟨4323936152471090105628865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23060992813179147230020613 4323936152471090105628865)
                ·
                  refine ⟨3242952114353317579221649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4323936152471090105628865 3242952114353317579221649)
                  ·
                    refine ⟨2432214085764988184416237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3242952114353317579221649 2432214085764988184416237)
                    ·
                      refine ⟨912080282161870569156089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2432214085764988184416237 912080282161870569156089)
                      ·
                        rfl

theorem cell23_1776270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_1776270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1776270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1776270 prefixEnd_1776270 := by exact prefixLift 1776270
  have htrace : WordTrace (prefixWord ++ tailWord_1776270) baseStart_1776270 baseEnd_1776270 := by
    simpa [prefixWord, tailWord_1776270, baseEnd_1776270] using wordTrace_append hprefix tailTrace_1776270
  have hstable : (prefixWord ++ tailWord_1776270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776270).length < 2 ^ (prefixWord ++ tailWord_1776270).sum := by decide
  have hdescent : baseEnd_1776270 < baseStart_1776270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776303 : List Nat := [1, 1, 2, 1, 2, 5, 2, 1, 3, 5]
def baseStart_1776303 : Nat := 118140960795 + 1776303 * 2 ^ 59
def prefixEnd_1776303 : Nat := 4983230072969 + 3 ^ 40 * 1776303 * 2
def baseEnd_1776303 : Nat := 304032409007822980014479

theorem tailTrace_1776303 : CollatzResearch.WordTrace tailWord_1776303 prefixEnd_1776303 304032409007822980014479 := by
  unfold tailWord_1776303
  simp only [CollatzResearch.WordTrace]
  refine ⟨64787092883765074245117563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43191395255843382830078375 64787092883765074245117563)
  ·
    refine ⟨97180639325647611367676345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64787092883765074245117563 97180639325647611367676345)
    ·
      refine ⟨72885479494235708525757259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97180639325647611367676345 72885479494235708525757259)
      ·
        refine ⟨109328219241353562788635889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72885479494235708525757259 109328219241353562788635889)
        ·
          refine ⟨81996164431015172091476917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109328219241353562788635889 81996164431015172091476917)
          ·
            refine ⟨7687140415407672383575961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81996164431015172091476917 7687140415407672383575961)
            ·
              refine ⟨5765355311555754287681971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7687140415407672383575961 5765355311555754287681971)
              ·
                refine ⟨8648032967333631431522957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5765355311555754287681971 8648032967333631431522957)
                ·
                  refine ⟨3243012362750111786821109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8648032967333631431522957 3243012362750111786821109)
                  ·
                    refine ⟨304032409007822980014479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3243012362750111786821109 304032409007822980014479)
                    ·
                      rfl

theorem cell23_1776303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 3, 5].length) (baseStart_1776303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1776303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1776303 prefixEnd_1776303 := by exact prefixLift 1776303
  have htrace : WordTrace (prefixWord ++ tailWord_1776303) baseStart_1776303 baseEnd_1776303 := by
    simpa [prefixWord, tailWord_1776303, baseEnd_1776303] using wordTrace_append hprefix tailTrace_1776303
  have hstable : (prefixWord ++ tailWord_1776303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776303).length < 2 ^ (prefixWord ++ tailWord_1776303).sum := by decide
  have hdescent : baseEnd_1776303 < baseStart_1776303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776320 : List Nat := [2, 1, 1, 2, 4, 3, 1, 3, 1, 5]
def baseStart_1776320 : Nat := 118140960795 + 1776320 * 2 ^ 59
def prefixEnd_1776320 : Nat := 4983230072969 + 3 ^ 40 * 1776320 * 2
def baseEnd_1776320 : Nat := 304035318731531791176953

theorem tailTrace_1776320 : CollatzResearch.WordTrace tailWord_1776320 prefixEnd_1776320 304035318731531791176953 := by
  unfold tailWord_1776320
  simp only [CollatzResearch.WordTrace]
  refine ⟨32393856462351743074243207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43191808616468990765657609 32393856462351743074243207)
  ·
    refine ⟨48590784693527614611364811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32393856462351743074243207 48590784693527614611364811)
    ·
      refine ⟨72886177040291421917047217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48590784693527614611364811 72886177040291421917047217)
      ·
        refine ⟨54664632780218566437785413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72886177040291421917047217 54664632780218566437785413)
        ·
          refine ⟨10249618646290981207084765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54664632780218566437785413 10249618646290981207084765)
          ·
            refine ⟨3843606992359117952656787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10249618646290981207084765 3843606992359117952656787)
            ·
              refine ⟨5765410488538676928985181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3843606992359117952656787 5765410488538676928985181)
              ·
                refine ⟨2162028933202003848369443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5765410488538676928985181 2162028933202003848369443)
                ·
                  refine ⟨3243043399803005772554165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2162028933202003848369443 3243043399803005772554165)
                  ·
                    refine ⟨304035318731531791176953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3243043399803005772554165 304035318731531791176953)
                    ·
                      rfl

theorem cell23_1776320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 3, 1, 5].length) (baseStart_1776320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1776320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1776320 prefixEnd_1776320 := by exact prefixLift 1776320
  have htrace : WordTrace (prefixWord ++ tailWord_1776320) baseStart_1776320 baseEnd_1776320 := by
    simpa [prefixWord, tailWord_1776320, baseEnd_1776320] using wordTrace_append hprefix tailTrace_1776320
  have hstable : (prefixWord ++ tailWord_1776320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776320).length < 2 ^ (prefixWord ++ tailWord_1776320).sum := by decide
  have hdescent : baseEnd_1776320 < baseStart_1776320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776334 : List Nat := [4, 1, 1, 1, 3, 2, 2, 4, 1, 1, 3]
def baseStart_1776334 : Nat := 118140960795 + 1776334 * 2 ^ 59
def prefixEnd_1776334 : Nat := 4983230072969 + 3 ^ 40 * 1776334 * 2
def baseEnd_1776334 : Nat := 912113144923758318755795

theorem tailTrace_1776334 : CollatzResearch.WordTrace tailWord_1776334 prefixEnd_1776334 912113144923758318755795 := by
  unfold tailWord_1776334
  simp only [CollatzResearch.WordTrace]
  refine ⟨8098527943331595817437007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43192149031101844359664037 8098527943331595817437007)
  ·
    refine ⟨12147791914997393726155511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8098527943331595817437007 12147791914997393726155511)
    ·
      refine ⟨18221687872496090589233267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12147791914997393726155511 18221687872496090589233267)
      ·
        refine ⟨27332531808744135883849901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18221687872496090589233267 27332531808744135883849901)
        ·
          refine ⟨10249699428279050956443713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27332531808744135883849901 10249699428279050956443713)
          ·
            refine ⟨7687274571209288217332785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10249699428279050956443713 7687274571209288217332785)
            ·
              refine ⟨5765455928406966162999589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7687274571209288217332785 5765455928406966162999589)
              ·
                refine ⟨1081022986576306155562423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5765455928406966162999589 1081022986576306155562423)
                ·
                  refine ⟨1621534479864459233343635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1081022986576306155562423 1621534479864459233343635)
                  ·
                    refine ⟨2432301719796688850015453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1621534479864459233343635 2432301719796688850015453)
                    ·
                      refine ⟨912113144923758318755795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2432301719796688850015453 912113144923758318755795)
                      ·
                        rfl

theorem cell23_1776334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 4, 1, 1, 3].length) (baseStart_1776334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1776334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1776334 prefixEnd_1776334 := by exact prefixLift 1776334
  have htrace : WordTrace (prefixWord ++ tailWord_1776334) baseStart_1776334 baseEnd_1776334 := by
    simpa [prefixWord, tailWord_1776334, baseEnd_1776334] using wordTrace_append hprefix tailTrace_1776334
  have hstable : (prefixWord ++ tailWord_1776334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776334).length < 2 ^ (prefixWord ++ tailWord_1776334).sum := by decide
  have hdescent : baseEnd_1776334 < baseStart_1776334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776343 : List Nat := [1, 1, 3, 2, 1, 4, 1, 1, 3, 1, 5]
def baseStart_1776343 : Nat := 118140960795 + 1776343 * 2 ^ 59
def prefixEnd_1776343 : Nat := 4983230072969 + 3 ^ 40 * 1776343 * 2
def baseEnd_1776343 : Nat := 912117766249648783543253

theorem tailTrace_1776343 : CollatzResearch.WordTrace tailWord_1776343 prefixEnd_1776343 912117766249648783543253 := by
  unfold tailWord_1776343
  simp only [CollatzResearch.WordTrace]
  refine ⟨64788551803620161076573683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43192367869080107384382455 64788551803620161076573683)
  ·
    refine ⟨97182827705430241614860525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64788551803620161076573683 97182827705430241614860525)
    ·
      refine ⟨36443560389536340605572697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97182827705430241614860525 36443560389536340605572697)
      ·
        refine ⟨27332670292152255454179523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36443560389536340605572697 27332670292152255454179523)
        ·
          refine ⟨40999005438228383181269285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27332670292152255454179523 40999005438228383181269285)
          ·
            refine ⟨7687313519667821846487991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40999005438228383181269285 7687313519667821846487991)
            ·
              refine ⟨11530970279501732769731987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7687313519667821846487991 11530970279501732769731987)
              ·
                refine ⟨17296455419252599154597981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11530970279501732769731987 17296455419252599154597981)
                ·
                  refine ⟨6486170782219724682974243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17296455419252599154597981 6486170782219724682974243)
                  ·
                    refine ⟨9729256173329587024461365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6486170782219724682974243 9729256173329587024461365)
                    ·
                      refine ⟨912117766249648783543253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9729256173329587024461365 912117766249648783543253)
                      ·
                        rfl

theorem cell23_1776343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_1776343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1776343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1776343 prefixEnd_1776343 := by exact prefixLift 1776343
  have htrace : WordTrace (prefixWord ++ tailWord_1776343) baseStart_1776343 baseEnd_1776343 := by
    simpa [prefixWord, tailWord_1776343, baseEnd_1776343] using wordTrace_append hprefix tailTrace_1776343
  have hstable : (prefixWord ++ tailWord_1776343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776343).length < 2 ^ (prefixWord ++ tailWord_1776343).sum := by decide
  have hdescent : baseEnd_1776343 < baseStart_1776343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776357 : List Nat := [1, 3, 1, 4, 1, 3, 2, 2, 1, 1, 4]
def baseStart_1776357 : Nat := 118140960795 + 1776357 * 2 ^ 59
def prefixEnd_1776357 : Nat := 4983230072969 + 3 ^ 40 * 1776357 * 2
def baseEnd_1776357 : Nat := 912124954978811728768189

theorem tailTrace_1776357 : CollatzResearch.WordTrace tailWord_1776357 prefixEnd_1776357 912124954978811728768189 := by
  unfold tailWord_1776357
  simp only [CollatzResearch.WordTrace]
  refine ⟨64789062425569441467583325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43192708283712960978388883 64789062425569441467583325)
  ·
    refine ⟨24295898409588540550343747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64789062425569441467583325 24295898409588540550343747)
    ·
      refine ⟨36443847614382810825515621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24295898409588540550343747 36443847614382810825515621)
      ·
        refine ⟨6833221427696777029784179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36443847614382810825515621 6833221427696777029784179)
        ·
          refine ⟨10249832141545165544676269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6833221427696777029784179 10249832141545165544676269)
          ·
            refine ⟨3843687053079437079253601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10249832141545165544676269 3843687053079437079253601)
            ·
              refine ⟨2882765289809577809440201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3843687053079437079253601 2882765289809577809440201)
              ·
                refine ⟨2162073967357183357080151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2882765289809577809440201 2162073967357183357080151)
                ·
                  refine ⟨3243110951035775035620227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2162073967357183357080151 3243110951035775035620227)
                  ·
                    refine ⟨4864666426553662553430341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3243110951035775035620227 4864666426553662553430341)
                    ·
                      refine ⟨912124954978811728768189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4864666426553662553430341 912124954978811728768189)
                      ·
                        rfl

theorem cell23_1776357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_1776357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1776357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1776357 prefixEnd_1776357 := by exact prefixLift 1776357
  have htrace : WordTrace (prefixWord ++ tailWord_1776357) baseStart_1776357 baseEnd_1776357 := by
    simpa [prefixWord, tailWord_1776357, baseEnd_1776357] using wordTrace_append hprefix tailTrace_1776357
  have hstable : (prefixWord ++ tailWord_1776357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776357).length < 2 ^ (prefixWord ++ tailWord_1776357).sum := by decide
  have hdescent : baseEnd_1776357 < baseStart_1776357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776391 : List Nat := [1, 1, 4, 4, 1, 3, 1, 1, 3, 2, 2]
def baseStart_1776391 : Nat := 118140960795 + 1776391 * 2 ^ 59
def prefixEnd_1776391 : Nat := 4983230072969 + 3 ^ 40 * 1776391 * 2
def baseEnd_1776391 : Nat := 912142413321064595743033

theorem tailTrace_1776391 : CollatzResearch.WordTrace tailWord_1776391 prefixEnd_1776391 912142413321064595743033 := by
  unfold tailWord_1776391
  simp only [CollatzResearch.WordTrace]
  refine ⟨64790302507446265274321027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43193535004964176849547351 64790302507446265274321027)
  ·
    refine ⟨97185453761169397911481541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64790302507446265274321027 97185453761169397911481541)
    ·
      refine ⟨18222272580219262108402789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97185453761169397911481541 18222272580219262108402789)
      ·
        refine ⟨3416676108791111645325523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18222272580219262108402789 3416676108791111645325523)
        ·
          refine ⟨5125014163186667467988285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3416676108791111645325523 5125014163186667467988285)
          ·
            refine ⟨1921880311195000300495607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5125014163186667467988285 1921880311195000300495607)
            ·
              refine ⟨2882820466792500450743411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1921880311195000300495607 2882820466792500450743411)
              ·
                refine ⟨4324230700188750676115117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2882820466792500450743411 4324230700188750676115117)
                ·
                  refine ⟨1621586512570781503543169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4324230700188750676115117 1621586512570781503543169)
                  ·
                    refine ⟨1216189884428086127657377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1621586512570781503543169 1216189884428086127657377)
                    ·
                      refine ⟨912142413321064595743033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1216189884428086127657377 912142413321064595743033)
                      ·
                        rfl

theorem cell23_1776391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_1776391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1776391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1776391 prefixEnd_1776391 := by exact prefixLift 1776391
  have htrace : WordTrace (prefixWord ++ tailWord_1776391) baseStart_1776391 baseEnd_1776391 := by
    simpa [prefixWord, tailWord_1776391, baseEnd_1776391] using wordTrace_append hprefix tailTrace_1776391
  have hstable : (prefixWord ++ tailWord_1776391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776391).length < 2 ^ (prefixWord ++ tailWord_1776391).sum := by decide
  have hdescent : baseEnd_1776391 < baseStart_1776391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776417 : List Nat := [1, 2, 3, 2, 1, 2, 3, 1, 3, 3, 2]
def baseStart_1776417 : Nat := 118140960795 + 1776417 * 2 ^ 59
def prefixEnd_1776417 : Nat := 4983230072969 + 3 ^ 40 * 1776417 * 2
def baseEnd_1776417 : Nat := 912155763818081494017913

theorem tailTrace_1776417 : CollatzResearch.WordTrace tailWord_1776417 prefixEnd_1776417 912155763818081494017913 := by
  unfold tailWord_1776417
  simp only [CollatzResearch.WordTrace]
  refine ⟨64791250805352071714767505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43194167203568047809845003 64791250805352071714767505)
  ·
    refine ⟨48593438104014053786075629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64791250805352071714767505 48593438104014053786075629)
    ·
      refine ⟨18222539289005270169778361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48593438104014053786075629 18222539289005270169778361)
      ·
        refine ⟨13666904466753952627333771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18222539289005270169778361 13666904466753952627333771)
        ·
          refine ⟨20500356700130928941000657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13666904466753952627333771 20500356700130928941000657)
          ·
            refine ⟨15375267525098196705750493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20500356700130928941000657 15375267525098196705750493)
            ·
              refine ⟨5765725321911823764656435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15375267525098196705750493 5765725321911823764656435)
              ·
                refine ⟨8648587982867735646984653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5765725321911823764656435 8648587982867735646984653)
                ·
                  refine ⟨3243220493575400867619245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8648587982867735646984653 3243220493575400867619245)
                  ·
                    refine ⟨1216207685090775325357217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3243220493575400867619245 1216207685090775325357217)
                    ·
                      refine ⟨912155763818081494017913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1216207685090775325357217 912155763818081494017913)
                      ·
                        rfl

theorem cell23_1776417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 3, 3, 2].length) (baseStart_1776417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1776417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1776417 prefixEnd_1776417 := by exact prefixLift 1776417
  have htrace : WordTrace (prefixWord ++ tailWord_1776417) baseStart_1776417 baseEnd_1776417 := by
    simpa [prefixWord, tailWord_1776417, baseEnd_1776417] using wordTrace_append hprefix tailTrace_1776417
  have hstable : (prefixWord ++ tailWord_1776417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776417).length < 2 ^ (prefixWord ++ tailWord_1776417).sum := by decide
  have hdescent : baseEnd_1776417 < baseStart_1776417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776460 : List Nat := [2, 2, 1, 3, 3, 1, 1, 1, 1, 4, 4]
def baseStart_1776460 : Nat := 118140960795 + 1776460 * 2 ^ 59
def prefixEnd_1776460 : Nat := 4983230072969 + 3 ^ 40 * 1776460 * 2
def baseEnd_1776460 : Nat := 912177843486224825780215

theorem tailTrace_1776460 : CollatzResearch.WordTrace tailWord_1776460 prefixEnd_1776460 912177843486224825780215 := by
  unfold tailWord_1776460
  simp only [CollatzResearch.WordTrace]
  refine ⟨32396409572098145029291417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43195212762797526705721889 32396409572098145029291417)
  ·
    refine ⟨24297307179073608771968563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32396409572098145029291417 24297307179073608771968563)
    ·
      refine ⟨36445960768610413157952845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24297307179073608771968563 36445960768610413157952845)
      ·
        refine ⟨13667235288228904934232317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36445960768610413157952845 13667235288228904934232317)
        ·
          refine ⟨5125213233085839350337119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13667235288228904934232317 5125213233085839350337119)
          ·
            refine ⟨7687819849628759025505679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5125213233085839350337119 7687819849628759025505679)
            ·
              refine ⟨11531729774443138538258519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7687819849628759025505679 11531729774443138538258519)
              ·
                refine ⟨17297594661664707807387779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11531729774443138538258519 17297594661664707807387779)
                ·
                  refine ⟨25946391992497061711081669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17297594661664707807387779 25946391992497061711081669)
                  ·
                    refine ⟨4864948498593199070827813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25946391992497061711081669 4864948498593199070827813)
                    ·
                      refine ⟨912177843486224825780215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4864948498593199070827813 912177843486224825780215)
                      ·
                        rfl

theorem cell23_1776460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_1776460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1776460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1776460 prefixEnd_1776460 := by exact prefixLift 1776460
  have htrace : WordTrace (prefixWord ++ tailWord_1776460) baseStart_1776460 baseEnd_1776460 := by
    simpa [prefixWord, tailWord_1776460, baseEnd_1776460] using wordTrace_append hprefix tailTrace_1776460
  have hstable : (prefixWord ++ tailWord_1776460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776460).length < 2 ^ (prefixWord ++ tailWord_1776460).sum := by decide
  have hdescent : baseEnd_1776460 < baseStart_1776460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776464 : List Nat := [2, 1, 1, 1, 1, 4, 4, 3, 2, 2, 2]
def baseStart_1776464 : Nat := 118140960795 + 1776464 * 2 ^ 59
def prefixEnd_1776464 : Nat := 4983230072969 + 3 ^ 40 * 1776464 * 2
def baseEnd_1776464 : Nat := 912179897408842810130197

theorem tailTrace_1776464 : CollatzResearch.WordTrace tailWord_1776464 prefixEnd_1776464 912179897408842810130197 := by
  unfold tailWord_1776464
  simp only [CollatzResearch.WordTrace]
  refine ⟨32396482518090899370864223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43195310024121199161152297 32396482518090899370864223)
  ·
    refine ⟨48594723777136349056296335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32396482518090899370864223 48594723777136349056296335)
    ·
      refine ⟨72892085665704523584444503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48594723777136349056296335 72892085665704523584444503)
      ·
        refine ⟨109338128498556785376666755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72892085665704523584444503 109338128498556785376666755)
        ·
          refine ⟨164007192747835178065000133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109338128498556785376666755 164007192747835178065000133)
          ·
            refine ⟨30751348640219095887187525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 164007192747835178065000133 30751348640219095887187525)
            ·
              refine ⟨5765877870041080478847661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30751348640219095887187525 5765877870041080478847661)
              ·
                refine ⟨2162204201265405179567873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5765877870041080478847661 2162204201265405179567873)
                ·
                  refine ⟨1621653150949053884675905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2162204201265405179567873 1621653150949053884675905)
                  ·
                    refine ⟨1216239863211790413506929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1621653150949053884675905 1216239863211790413506929)
                    ·
                      refine ⟨912179897408842810130197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1216239863211790413506929 912179897408842810130197)
                      ·
                        rfl

theorem cell23_1776464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 3, 2, 2, 2].length) (baseStart_1776464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1776464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1776464 prefixEnd_1776464 := by exact prefixLift 1776464
  have htrace : WordTrace (prefixWord ++ tailWord_1776464) baseStart_1776464 baseEnd_1776464 := by
    simpa [prefixWord, tailWord_1776464, baseEnd_1776464] using wordTrace_append hprefix tailTrace_1776464
  have hstable : (prefixWord ++ tailWord_1776464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776464).length < 2 ^ (prefixWord ++ tailWord_1776464).sum := by decide
  have hdescent : baseEnd_1776464 < baseStart_1776464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776480 : List Nat := [2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 3]
def baseStart_1776480 : Nat := 118140960795 + 1776480 * 2 ^ 59
def prefixEnd_1776480 : Nat := 4983230072969 + 3 ^ 40 * 1776480 * 2
def baseEnd_1776480 : Nat := 912188113099314747530123

theorem tailTrace_1776480 : CollatzResearch.WordTrace tailWord_1776480 prefixEnd_1776480 912188113099314747530123 := by
  unfold tailWord_1776480
  simp only [CollatzResearch.WordTrace]
  refine ⟨32396774302061916737155447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43195699069415888982873929 32396774302061916737155447)
  ·
    refine ⟨48595161453092875105733171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32396774302061916737155447 48595161453092875105733171)
    ·
      refine ⟨72892742179639312658599757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48595161453092875105733171 72892742179639312658599757)
      ·
        refine ⟨27334778317364742246974909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72892742179639312658599757 27334778317364742246974909)
        ·
          refine ⟨10250541869011778342615591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27334778317364742246974909 10250541869011778342615591)
          ·
            refine ⟨15375812803517667513923387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10250541869011778342615591 15375812803517667513923387)
            ·
              refine ⟨23063719205276501270885081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15375812803517667513923387 23063719205276501270885081)
              ·
                refine ⟨17297789403957375953163811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23063719205276501270885081 17297789403957375953163811)
                ·
                  refine ⟨25946684105936063929745717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17297789403957375953163811 25946684105936063929745717)
                  ·
                    refine ⟨2432501634931505993413661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25946684105936063929745717 2432501634931505993413661)
                    ·
                      refine ⟨912188113099314747530123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2432501634931505993413661 912188113099314747530123)
                      ·
                        rfl

theorem cell23_1776480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 3].length) (baseStart_1776480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1776480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1776480 prefixEnd_1776480 := by exact prefixLift 1776480
  have htrace : WordTrace (prefixWord ++ tailWord_1776480) baseStart_1776480 baseEnd_1776480 := by
    simpa [prefixWord, tailWord_1776480, baseEnd_1776480] using wordTrace_append hprefix tailTrace_1776480
  have hstable : (prefixWord ++ tailWord_1776480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776480).length < 2 ^ (prefixWord ++ tailWord_1776480).sum := by decide
  have hdescent : baseEnd_1776480 < baseStart_1776480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776487 : List Nat := [1, 1, 5, 1, 2, 2, 1, 5, 5]
def baseStart_1776487 : Nat := 118140960795 + 1776487 * 2 ^ 59
def prefixEnd_1776487 : Nat := 4983230072969 + 3 ^ 40 * 1776487 * 2
def baseEnd_1776487 : Nat := 101354634162655135571399

theorem tailTrace_1776487 : CollatzResearch.WordTrace tailWord_1776487 prefixEnd_1776487 101354634162655135571399 := by
  unfold tailWord_1776487
  simp only [CollatzResearch.WordTrace]
  refine ⟨64793803915098473669815715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43195869276732315779877143 64793803915098473669815715)
  ·
    refine ⟨97190705872647710504723573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64793803915098473669815715 97190705872647710504723573)
    ·
      refine ⟨9111628675560722859817835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97190705872647710504723573 9111628675560722859817835)
      ·
        refine ⟨13667443013341084289726753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9111628675560722859817835 13667443013341084289726753)
        ·
          refine ⟨10250582260005813217295065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13667443013341084289726753 10250582260005813217295065)
          ·
            refine ⟨7687936695004359912971299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10250582260005813217295065 7687936695004359912971299)
            ·
              refine ⟨11531905042506539869456949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7687936695004359912971299 11531905042506539869456949)
              ·
                refine ⟨1081116097734988112761589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11531905042506539869456949 1081116097734988112761589)
                ·
                  refine ⟨101354634162655135571399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1081116097734988112761589 101354634162655135571399)
                  ·
                    rfl

theorem cell23_1776487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 5, 5].length) (baseStart_1776487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1776487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1776487 prefixEnd_1776487 := by exact prefixLift 1776487
  have htrace : WordTrace (prefixWord ++ tailWord_1776487) baseStart_1776487 baseEnd_1776487 := by
    simpa [prefixWord, tailWord_1776487, baseEnd_1776487] using wordTrace_append hprefix tailTrace_1776487
  have hstable : (prefixWord ++ tailWord_1776487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776487).length < 2 ^ (prefixWord ++ tailWord_1776487).sum := by decide
  have hdescent : baseEnd_1776487 < baseStart_1776487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776566 : List Nat := [5, 1, 4, 1, 2, 1, 2, 1, 2, 2, 2]
def baseStart_1776566 : Nat := 118140960795 + 1776566 * 2 ^ 59
def prefixEnd_1776566 : Nat := 4983230072969 + 3 ^ 40 * 1776566 * 2
def baseEnd_1776566 : Nat := 912232272435601411054729

theorem tailTrace_1776566 : CollatzResearch.WordTrace tailWord_1776566 prefixEnd_1776566 912232272435601411054729 := by
  unfold tailWord_1776566
  simp only [CollatzResearch.WordTrace]
  refine ⟨4049792830113266885121347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43197790187874846774627701 4049792830113266885121347)
  ·
    refine ⟨6074689245169900327682021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4049792830113266885121347 6074689245169900327682021)
    ·
      refine ⟨1139004233469356311440379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6074689245169900327682021 1139004233469356311440379)
      ·
        refine ⟨1708506350204034467160569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1139004233469356311440379 1708506350204034467160569)
        ·
          refine ⟨1281379762653025850370427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1708506350204034467160569 1281379762653025850370427)
          ·
            refine ⟨1922069643979538775555641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1281379762653025850370427 1922069643979538775555641)
            ·
              refine ⟨1441552232984654081666731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1922069643979538775555641 1441552232984654081666731)
              ·
                refine ⟨2162328349476981122500097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1441552232984654081666731 2162328349476981122500097)
                ·
                  refine ⟨1621746262107735841875073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2162328349476981122500097 1621746262107735841875073)
                  ·
                    refine ⟨1216309696580801881406305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1621746262107735841875073 1216309696580801881406305)
                    ·
                      refine ⟨912232272435601411054729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1216309696580801881406305 912232272435601411054729)
                      ·
                        rfl

theorem cell23_1776566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_1776566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1776566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1776566 prefixEnd_1776566 := by exact prefixLift 1776566
  have htrace : WordTrace (prefixWord ++ tailWord_1776566) baseStart_1776566 baseEnd_1776566 := by
    simpa [prefixWord, tailWord_1776566, baseEnd_1776566] using wordTrace_append hprefix tailTrace_1776566
  have hstable : (prefixWord ++ tailWord_1776566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776566).length < 2 ^ (prefixWord ++ tailWord_1776566).sum := by decide
  have hdescent : baseEnd_1776566 < baseStart_1776566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776627 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 4, 6, 2]
def baseStart_1776627 : Nat := 118140960795 + 1776627 * 2 ^ 59
def prefixEnd_1776627 : Nat := 4983230072969 + 3 ^ 40 * 1776627 * 2
def baseEnd_1776627 : Nat := 912263594755525672391947

theorem tailTrace_1776627 : CollatzResearch.WordTrace tailWord_1776627 prefixEnd_1776627 912263594755525672391947 := by
  unfold tailWord_1776627
  simp only [CollatzResearch.WordTrace]
  refine ⟨64798910134591277579912135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43199273423060851719941423 64798910134591277579912135)
  ·
    refine ⟨97198365201886916369868203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64798910134591277579912135 97198365201886916369868203)
    ·
      refine ⟨145797547802830374554802305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97198365201886916369868203 145797547802830374554802305)
      ·
        refine ⟨109348160852122780916101729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145797547802830374554802305 109348160852122780916101729)
        ·
          refine ⟨82011120639092085687076297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109348160852122780916101729 82011120639092085687076297)
          ·
            refine ⟨61508340479319064265307223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82011120639092085687076297 61508340479319064265307223)
            ·
              refine ⟨92262510718978596397960835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61508340479319064265307223 92262510718978596397960835)
              ·
                refine ⟨138393766078467894596941253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92262510718978596397960835 138393766078467894596941253)
                ·
                  refine ⟨25948831139712730236926485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138393766078467894596941253 25948831139712730236926485)
                  ·
                    refine ⟨1216351459674034229855929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25948831139712730236926485 1216351459674034229855929)
                    ·
                      refine ⟨912263594755525672391947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1216351459674034229855929 912263594755525672391947)
                      ·
                        rfl

theorem cell23_1776627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 6, 2].length) (baseStart_1776627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1776627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1776627 prefixEnd_1776627 := by exact prefixLift 1776627
  have htrace : WordTrace (prefixWord ++ tailWord_1776627) baseStart_1776627 baseEnd_1776627 := by
    simpa [prefixWord, tailWord_1776627, baseEnd_1776627] using wordTrace_append hprefix tailTrace_1776627
  have hstable : (prefixWord ++ tailWord_1776627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776627).length < 2 ^ (prefixWord ++ tailWord_1776627).sum := by decide
  have hdescent : baseEnd_1776627 < baseStart_1776627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776637 : List Nat := [1, 4, 1, 1, 1, 2, 1, 2, 6, 4]
def baseStart_1776637 : Nat := 118140960795 + 1776637 * 2 ^ 59
def prefixEnd_1776637 : Nat := 4983230072969 + 3 ^ 40 * 1776637 * 2
def baseEnd_1776637 : Nat := 304089576520690211088967

theorem tailTrace_1776637 : CollatzResearch.WordTrace tailWord_1776637 prefixEnd_1776637 304089576520690211088967 := by
  unfold tailWord_1776637
  simp only [CollatzResearch.WordTrace]
  refine ⟨64799274864555049287776165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43199516576370032858517443 64799274864555049287776165)
  ·
    refine ⟨12149864037104071741458031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64799274864555049287776165 12149864037104071741458031)
    ·
      refine ⟨18224796055656107612187047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12149864037104071741458031 18224796055656107612187047)
      ·
        refine ⟨27337194083484161418280571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18224796055656107612187047 27337194083484161418280571)
        ·
          refine ⟨41005791125226242127420857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27337194083484161418280571 41005791125226242127420857)
          ·
            refine ⟨30754343343919681595565643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41005791125226242127420857 30754343343919681595565643)
            ·
              refine ⟨46131515015879522393348465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30754343343919681595565643 46131515015879522393348465)
              ·
                refine ⟨34598636261909641795011349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46131515015879522393348465 34598636261909641795011349)
                ·
                  refine ⟨1621811074777014459141157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 34598636261909641795011349 1621811074777014459141157)
                  ·
                    refine ⟨304089576520690211088967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1621811074777014459141157 304089576520690211088967)
                    ·
                      rfl

theorem cell23_1776637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 6, 4].length) (baseStart_1776637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1776637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1776637 prefixEnd_1776637 := by exact prefixLift 1776637
  have htrace : WordTrace (prefixWord ++ tailWord_1776637) baseStart_1776637 baseEnd_1776637 := by
    simpa [prefixWord, tailWord_1776637, baseEnd_1776637] using wordTrace_append hprefix tailTrace_1776637
  have hstable : (prefixWord ++ tailWord_1776637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776637).length < 2 ^ (prefixWord ++ tailWord_1776637).sum := by decide
  have hdescent : baseEnd_1776637 < baseStart_1776637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776638 : List Nat := [4, 2, 2, 2, 2, 1, 1, 2, 3, 1, 3]
def baseStart_1776638 : Nat := 118140960795 + 1776638 * 2 ^ 59
def prefixEnd_1776638 : Nat := 4983230072969 + 3 ^ 40 * 1776638 * 2
def baseEnd_1776638 : Nat := 912269243042725129354397

theorem tailTrace_1776638 : CollatzResearch.WordTrace tailWord_1776638 prefixEnd_1776638 912269243042725129354397 := by
  unfold tailWord_1776638
  simp only [CollatzResearch.WordTrace]
  refine ⟨8099913917193928307320321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43199540891700950972375045 8099913917193928307320321)
  ·
    refine ⟨6074935437895446230490241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8099913917193928307320321 6074935437895446230490241)
    ·
      refine ⟨4556201578421584672867681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6074935437895446230490241 4556201578421584672867681)
      ·
        refine ⟨3417151183816188504650761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4556201578421584672867681 3417151183816188504650761)
        ·
          refine ⟨2562863387862141378488071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3417151183816188504650761 2562863387862141378488071)
          ·
            refine ⟨3844295081793212067732107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2562863387862141378488071 3844295081793212067732107)
            ·
              refine ⟨5766442622689818101598161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3844295081793212067732107 5766442622689818101598161)
              ·
                refine ⟨4324831967017363576198621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5766442622689818101598161 4324831967017363576198621)
                ·
                  refine ⟨1621811987631511341074483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4324831967017363576198621 1621811987631511341074483)
                  ·
                    refine ⟨2432717981447267011611725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1621811987631511341074483 2432717981447267011611725)
                    ·
                      refine ⟨912269243042725129354397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2432717981447267011611725 912269243042725129354397)
                      ·
                        rfl

theorem cell23_1776638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_1776638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1776638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1776638 prefixEnd_1776638 := by exact prefixLift 1776638
  have htrace : WordTrace (prefixWord ++ tailWord_1776638) baseStart_1776638 baseEnd_1776638 := by
    simpa [prefixWord, tailWord_1776638, baseEnd_1776638] using wordTrace_append hprefix tailTrace_1776638
  have hstable : (prefixWord ++ tailWord_1776638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776638).length < 2 ^ (prefixWord ++ tailWord_1776638).sum := by decide
  have hdescent : baseEnd_1776638 < baseStart_1776638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776640 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 6]
def baseStart_1776640 : Nat := 118140960795 + 1776640 * 2 ^ 59
def prefixEnd_1776640 : Nat := 4983230072969 + 3 ^ 40 * 1776640 * 2
def baseEnd_1776640 : Nat := 912270270004034121529387

theorem tailTrace_1776640 : CollatzResearch.WordTrace tailWord_1776640 prefixEnd_1776640 912270270004034121529387 := by
  unfold tailWord_1776640
  simp only [CollatzResearch.WordTrace]
  refine ⟨32399692141772090400067687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43199589522362787200090249 32399692141772090400067687)
  ·
    refine ⟨48599538212658135600101531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32399692141772090400067687 48599538212658135600101531)
    ·
      refine ⟨72899307318987203400152297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48599538212658135600101531 72899307318987203400152297)
      ·
        refine ⟨54674480489240402550114223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72899307318987203400152297 54674480489240402550114223)
        ·
          refine ⟨82011720733860603825171335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54674480489240402550114223 82011720733860603825171335)
          ·
            refine ⟨123017581100790905737757003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82011720733860603825171335 123017581100790905737757003)
            ·
              refine ⟨184526371651186358606635505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123017581100790905737757003 184526371651186358606635505)
              ·
                refine ⟨138394778738389768954976629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184526371651186358606635505 138394778738389768954976629)
                ·
                  refine ⟨12974510506724040839529059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 138394778738389768954976629 12974510506724040839529059)
                  ·
                    refine ⟨19461765760086061259293589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12974510506724040839529059 19461765760086061259293589)
                    ·
                      refine ⟨912270270004034121529387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19461765760086061259293589 912270270004034121529387)
                      ·
                        rfl

theorem cell23_1776640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 6].length) (baseStart_1776640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1776640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1776640 prefixEnd_1776640 := by exact prefixLift 1776640
  have htrace : WordTrace (prefixWord ++ tailWord_1776640) baseStart_1776640 baseEnd_1776640 := by
    simpa [prefixWord, tailWord_1776640, baseEnd_1776640] using wordTrace_append hprefix tailTrace_1776640
  have hstable : (prefixWord ++ tailWord_1776640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776640).length < 2 ^ (prefixWord ++ tailWord_1776640).sum := by decide
  have hdescent : baseEnd_1776640 < baseStart_1776640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776661 : List Nat := [1, 3, 2, 1, 4, 1, 4, 1, 1, 1, 4]
def baseStart_1776661 : Nat := 118140960795 + 1776661 * 2 ^ 59
def prefixEnd_1776661 : Nat := 4983230072969 + 3 ^ 40 * 1776661 * 2
def baseEnd_1776661 : Nat := 912281053097778539366791

theorem tailTrace_1776661 : CollatzResearch.WordTrace tailWord_1776661 prefixEnd_1776661 912281053097778539366791 := by
  unfold tailWord_1776661
  simp only [CollatzResearch.WordTrace]
  refine ⟨64800150216468101386649837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43200100144312067591099891 64800150216468101386649837)
  ·
    refine ⟨24300056331175538019993689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64800150216468101386649837 24300056331175538019993689)
    ·
      refine ⟨18225042248381653514995267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24300056331175538019993689 18225042248381653514995267)
      ·
        refine ⟨27337563372572480272492901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18225042248381653514995267 27337563372572480272492901)
        ·
          refine ⟨5125793132357340051092419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27337563372572480272492901 5125793132357340051092419)
          ·
            refine ⟨7688689698536010076638629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5125793132357340051092419 7688689698536010076638629)
            ·
              refine ⟨1441629318475501889369743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7688689698536010076638629 1441629318475501889369743)
              ·
                refine ⟨2162443977713252834054615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1441629318475501889369743 2162443977713252834054615)
                ·
                  refine ⟨3243665966569879251081923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2162443977713252834054615 3243665966569879251081923)
                  ·
                    refine ⟨4865498949854818876622885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3243665966569879251081923 4865498949854818876622885)
                    ·
                      refine ⟨912281053097778539366791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4865498949854818876622885 912281053097778539366791)
                      ·
                        rfl

theorem cell23_1776661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 1, 1, 1, 4].length) (baseStart_1776661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1776661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1776661 prefixEnd_1776661 := by exact prefixLift 1776661
  have htrace : WordTrace (prefixWord ++ tailWord_1776661) baseStart_1776661 baseEnd_1776661 := by
    simpa [prefixWord, tailWord_1776661, baseEnd_1776661] using wordTrace_append hprefix tailTrace_1776661
  have hstable : (prefixWord ++ tailWord_1776661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776661).length < 2 ^ (prefixWord ++ tailWord_1776661).sum := by decide
  have hdescent : baseEnd_1776661 < baseStart_1776661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776671 : List Nat := [1, 1, 2, 4, 1, 5, 1, 2, 2, 4]
def baseStart_1776671 : Nat := 118140960795 + 1776671 * 2 ^ 59
def prefixEnd_1776671 : Nat := 4983230072969 + 3 ^ 40 * 1776671 * 2
def baseEnd_1776671 : Nat := 304095395968107833413915

theorem tailTrace_1776671 : CollatzResearch.WordTrace tailWord_1776671 prefixEnd_1776671 304095395968107833413915 := by
  unfold tailWord_1776671
  simp only [CollatzResearch.WordTrace]
  refine ⟨64800514946431873094513867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43200343297621248729675911 64800514946431873094513867)
  ·
    refine ⟨97200772419647809641770801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64800514946431873094513867 97200772419647809641770801)
    ·
      refine ⟨72900579314735857231328101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97200772419647809641770801 72900579314735857231328101)
      ·
        refine ⟨13668858621512973230874019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72900579314735857231328101 13668858621512973230874019)
        ·
          refine ⟨20503287932269459846311029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13668858621512973230874019 20503287932269459846311029)
          ·
            refine ⟨1922183243650261860591659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20503287932269459846311029 1922183243650261860591659)
            ·
              refine ⟨2883274865475392790887489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1922183243650261860591659 2883274865475392790887489)
              ·
                refine ⟨2162456149106544593165617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2883274865475392790887489 2162456149106544593165617)
                ·
                  refine ⟨1621842111829908444874213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2162456149106544593165617 1621842111829908444874213)
                  ·
                    refine ⟨304095395968107833413915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1621842111829908444874213 304095395968107833413915)
                    ·
                      rfl

theorem cell23_1776671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 2, 2, 4].length) (baseStart_1776671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1776671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1776671 prefixEnd_1776671 := by exact prefixLift 1776671
  have htrace : WordTrace (prefixWord ++ tailWord_1776671) baseStart_1776671 baseEnd_1776671 := by
    simpa [prefixWord, tailWord_1776671, baseEnd_1776671] using wordTrace_append hprefix tailTrace_1776671
  have hstable : (prefixWord ++ tailWord_1776671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776671).length < 2 ^ (prefixWord ++ tailWord_1776671).sum := by decide
  have hdescent : baseEnd_1776671 < baseStart_1776671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776721 : List Nat := [1, 2, 2, 1, 3, 1, 4, 3, 1, 3, 2]
def baseStart_1776721 : Nat := 118140960795 + 1776721 * 2 ^ 59
def prefixEnd_1776721 : Nat := 4983230072969 + 3 ^ 40 * 1776721 * 2
def baseEnd_1776721 : Nat := 912311861937048304616515

theorem tailTrace_1776721 : CollatzResearch.WordTrace tailWord_1776721 prefixEnd_1776721 912311861937048304616515 := by
  unfold tailWord_1776721
  simp only [CollatzResearch.WordTrace]
  refine ⟨64802338596250731633834017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43201559064167154422556011 64802338596250731633834017)
  ·
    refine ⟨48601753947188048725375513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64802338596250731633834017 48601753947188048725375513)
    ·
      refine ⟨36451315460391036544031635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48601753947188048725375513 36451315460391036544031635)
      ·
        refine ⟨54676973190586554816047453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36451315460391036544031635 54676973190586554816047453)
        ·
          refine ⟨20503864946469958056017795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54676973190586554816047453 20503864946469958056017795)
          ·
            refine ⟨30755797419704937084026693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20503864946469958056017795 30755797419704937084026693)
            ·
              refine ⟨5766712016194675703255005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30755797419704937084026693 5766712016194675703255005)
              ·
                refine ⟨2162517006073003388720627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5766712016194675703255005 2162517006073003388720627)
                ·
                  refine ⟨3243775509109505083080941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2162517006073003388720627 3243775509109505083080941)
                  ·
                    refine ⟨1216415815916064406155353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3243775509109505083080941 1216415815916064406155353)
                    ·
                      refine ⟨912311861937048304616515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1216415815916064406155353 912311861937048304616515)
                      ·
                        rfl

theorem cell23_1776721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 3, 1, 3, 2].length) (baseStart_1776721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1776721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1776721 prefixEnd_1776721 := by exact prefixLift 1776721
  have htrace : WordTrace (prefixWord ++ tailWord_1776721) baseStart_1776721 baseEnd_1776721 := by
    simpa [prefixWord, tailWord_1776721, baseEnd_1776721] using wordTrace_append hprefix tailTrace_1776721
  have hstable : (prefixWord ++ tailWord_1776721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776721).length < 2 ^ (prefixWord ++ tailWord_1776721).sum := by decide
  have hdescent : baseEnd_1776721 < baseStart_1776721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776791 : List Nat := [1, 1, 3, 3, 3, 2, 1, 4, 5]
def baseStart_1776791 : Nat := 118140960795 + 1776791 * 2 ^ 59
def prefixEnd_1776791 : Nat := 4983230072969 + 3 ^ 40 * 1776791 * 2
def baseEnd_1776791 : Nat := 101371978398095892304577

theorem tailTrace_1776791 : CollatzResearch.WordTrace tailWord_1776791 prefixEnd_1776791 101371978398095892304577 := by
  unfold tailWord_1776791
  simp only [CollatzResearch.WordTrace]
  refine ⟨64804891705997133588882227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43203261137331422392588151 64804891705997133588882227)
  ·
    refine ⟨97207337558995700383323341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64804891705997133588882227 97207337558995700383323341)
    ·
      refine ⟨36452751584623387643746253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97207337558995700383323341 36452751584623387643746253)
      ·
        refine ⟨13669781844233770366404845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36452751584623387643746253 13669781844233770366404845)
        ·
          refine ⟨5126168191587663887401817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13669781844233770366404845 5126168191587663887401817)
          ·
            refine ⟨3844626143690747915551363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5126168191587663887401817 3844626143690747915551363)
            ·
              refine ⟨5766939215536121873327045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3844626143690747915551363 5766939215536121873327045)
              ·
                refine ⟨1081301102913022851248821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5766939215536121873327045 1081301102913022851248821)
                ·
                  refine ⟨101371978398095892304577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1081301102913022851248821 101371978398095892304577)
                  ·
                    rfl

theorem cell23_1776791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 4, 5].length) (baseStart_1776791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1776791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1776791 prefixEnd_1776791 := by exact prefixLift 1776791
  have htrace : WordTrace (prefixWord ++ tailWord_1776791) baseStart_1776791 baseEnd_1776791 := by
    simpa [prefixWord, tailWord_1776791, baseEnd_1776791] using wordTrace_append hprefix tailTrace_1776791
  have hstable : (prefixWord ++ tailWord_1776791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776791).length < 2 ^ (prefixWord ++ tailWord_1776791).sum := by decide
  have hdescent : baseEnd_1776791 < baseStart_1776791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776824 : List Nat := [2, 1, 2, 1, 2, 1, 2, 5, 2, 1, 4]
def baseStart_1776824 : Nat := 118140960795 + 1776824 * 2 ^ 59
def prefixEnd_1776824 : Nat := 4983230072969 + 3 ^ 40 * 1776824 * 2
def baseEnd_1776824 : Nat := 912364750444461401628541

theorem tailTrace_1776824 : CollatzResearch.WordTrace tailWord_1776824 prefixEnd_1776824 912364750444461401628541 := by
  unfold tailWord_1776824
  simp only [CollatzResearch.WordTrace]
  refine ⟨32403047657438790112416763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43204063543251720149889017 32403047657438790112416763)
  ·
    refine ⟨48604571486158185168625145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32403047657438790112416763 48604571486158185168625145)
    ·
      refine ⟨36453428614618638876468859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48604571486158185168625145 36453428614618638876468859)
      ·
        refine ⟨54680142921927958314703289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36453428614618638876468859 54680142921927958314703289)
        ·
          refine ⟨41010107191445968736027467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54680142921927958314703289 41010107191445968736027467)
          ·
            refine ⟨61515160787168953104041201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41010107191445968736027467 61515160787168953104041201)
            ·
              refine ⟨46136370590376714828030901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61515160787168953104041201 46136370590376714828030901)
              ·
                refine ⟨4325284742847817015127897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46136370590376714828030901 4325284742847817015127897)
                ·
                  refine ⟨3243963557135862761345923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4325284742847817015127897 3243963557135862761345923)
                  ·
                    refine ⟨4865945335703794142018885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3243963557135862761345923 4865945335703794142018885)
                    ·
                      refine ⟨912364750444461401628541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4865945335703794142018885 912364750444461401628541)
                      ·
                        rfl

theorem cell23_1776824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5, 2, 1, 4].length) (baseStart_1776824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1776824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1776824 prefixEnd_1776824 := by exact prefixLift 1776824
  have htrace : WordTrace (prefixWord ++ tailWord_1776824) baseStart_1776824 baseEnd_1776824 := by
    simpa [prefixWord, tailWord_1776824, baseEnd_1776824] using wordTrace_append hprefix tailTrace_1776824
  have hstable : (prefixWord ++ tailWord_1776824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776824).length < 2 ^ (prefixWord ++ tailWord_1776824).sum := by decide
  have hdescent : baseEnd_1776824 < baseStart_1776824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776827 : List Nat := [1, 1, 1, 1, 1, 2, 4, 2, 2, 3, 5]
def baseStart_1776827 : Nat := 118140960795 + 1776827 * 2 ^ 59
def prefixEnd_1776827 : Nat := 4983230072969 + 3 ^ 40 * 1776827 * 2
def baseEnd_1776827 : Nat := 912366290886424889891027

theorem tailTrace_1776827 : CollatzResearch.WordTrace tailWord_1776827 prefixEnd_1776827 912366290886424889891027 := by
  unfold tailWord_1776827
  simp only [CollatzResearch.WordTrace]
  refine ⟨64806204733866711737192735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43204136489244474491461823 64806204733866711737192735)
  ·
    refine ⟨97209307100800067605789103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64806204733866711737192735 97209307100800067605789103)
    ·
      refine ⟨145813960651200101408683655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97209307100800067605789103 145813960651200101408683655)
      ·
        refine ⟨218720940976800152113025483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145813960651200101408683655 218720940976800152113025483)
        ·
          refine ⟨328081411465200228169538225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218720940976800152113025483 328081411465200228169538225)
          ·
            refine ⟨246061058598900171127153669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 328081411465200228169538225 246061058598900171127153669)
            ·
              refine ⟨46136448487293782086341313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 246061058598900171127153669 46136448487293782086341313)
              ·
                refine ⟨34602336365470336564755985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46136448487293782086341313 34602336365470336564755985)
                ·
                  refine ⟨25951752274102752423566989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34602336365470336564755985 25951752274102752423566989)
                  ·
                    refine ⟨9731907102788532158837621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25951752274102752423566989 9731907102788532158837621)
                    ·
                      refine ⟨912366290886424889891027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9731907102788532158837621 912366290886424889891027)
                      ·
                        rfl

theorem cell23_1776827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3, 5].length) (baseStart_1776827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1776827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1776827 prefixEnd_1776827 := by exact prefixLift 1776827
  have htrace : WordTrace (prefixWord ++ tailWord_1776827) baseStart_1776827 baseEnd_1776827 := by
    simpa [prefixWord, tailWord_1776827, baseEnd_1776827] using wordTrace_append hprefix tailTrace_1776827
  have hstable : (prefixWord ++ tailWord_1776827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776827).length < 2 ^ (prefixWord ++ tailWord_1776827).sum := by decide
  have hdescent : baseEnd_1776827 < baseStart_1776827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776908 : List Nat := [2, 2, 1, 2, 2, 3, 3, 1, 3, 1, 3]
def baseStart_1776908 : Nat := 118140960795 + 1776908 * 2 ^ 59
def prefixEnd_1776908 : Nat := 4983230072969 + 3 ^ 40 * 1776908 * 2
def baseEnd_1776908 : Nat := 912407882819439072978155

theorem tailTrace_1776908 : CollatzResearch.WordTrace tailWord_1776908 prefixEnd_1776908 912407882819439072978155 := by
  unfold tailWord_1776908
  simp only [CollatzResearch.WordTrace]
  refine ⟨32404579523286631285445689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43206106031048841713927585 32404579523286631285445689)
  ·
    refine ⟨24303434642464973464084267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32404579523286631285445689 24303434642464973464084267)
    ·
      refine ⟨36455151963697460196126401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24303434642464973464084267 36455151963697460196126401)
      ·
        refine ⟨27341363972773095147094801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36455151963697460196126401 27341363972773095147094801)
        ·
          refine ⟨20506022979579821360321101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27341363972773095147094801 20506022979579821360321101)
          ·
            refine ⟨7689758617342433010120413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20506022979579821360321101 7689758617342433010120413)
            ·
              refine ⟨2883659481503412378795155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7689758617342433010120413 2883659481503412378795155)
              ·
                refine ⟨4325489222255118568192733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2883659481503412378795155 4325489222255118568192733)
                ·
                  refine ⟨1622058458345669463072275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4325489222255118568192733 1622058458345669463072275)
                  ·
                    refine ⟨2433087687518504194608413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1622058458345669463072275 2433087687518504194608413)
                    ·
                      refine ⟨912407882819439072978155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2433087687518504194608413 912407882819439072978155)
                      ·
                        rfl

theorem cell23_1776908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 1, 3, 1, 3].length) (baseStart_1776908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1776908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1776908 prefixEnd_1776908 := by exact prefixLift 1776908
  have htrace : WordTrace (prefixWord ++ tailWord_1776908) baseStart_1776908 baseEnd_1776908 := by
    simpa [prefixWord, tailWord_1776908, baseEnd_1776908] using wordTrace_append hprefix tailTrace_1776908
  have hstable : (prefixWord ++ tailWord_1776908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776908).length < 2 ^ (prefixWord ++ tailWord_1776908).sum := by decide
  have hdescent : baseEnd_1776908 < baseStart_1776908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776931 : List Nat := [1, 1, 1, 4, 2, 4, 1, 1, 3, 1, 4]
def baseStart_1776931 : Nat := 118140960795 + 1776931 * 2 ^ 59
def prefixEnd_1776931 : Nat := 4983230072969 + 3 ^ 40 * 1776931 * 2
def baseEnd_1776931 : Nat := 912419692874492482990549

theorem tailTrace_1776931 : CollatzResearch.WordTrace tailWord_1776931 prefixEnd_1776931 912419692874492482990549 := by
  unfold tailWord_1776931
  simp only [CollatzResearch.WordTrace]
  refine ⟨64809997925489937498978647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43206665283659958332652431 64809997925489937498978647)
  ·
    refine ⟨97214996888234906248467971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64809997925489937498978647 97214996888234906248467971)
    ·
      refine ⟨145822495332352359372701957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97214996888234906248467971 145822495332352359372701957)
      ·
        refine ⟨27341717874816067382381617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145822495332352359372701957 27341717874816067382381617)
        ·
          refine ⟨20506288406112050536786213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27341717874816067382381617 20506288406112050536786213)
          ·
            refine ⟨3844929076146009475647415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20506288406112050536786213 3844929076146009475647415)
            ·
              refine ⟨5767393614219014213471123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3844929076146009475647415 5767393614219014213471123)
              ·
                refine ⟨8651090421328521320206685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5767393614219014213471123 8651090421328521320206685)
                ·
                  refine ⟨3244158907998195495077507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8651090421328521320206685 3244158907998195495077507)
                  ·
                    refine ⟨4866238361997293242616261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3244158907998195495077507 4866238361997293242616261)
                    ·
                      refine ⟨912419692874492482990549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4866238361997293242616261 912419692874492482990549)
                      ·
                        rfl

theorem cell23_1776931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 3, 1, 4].length) (baseStart_1776931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1776931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1776931 prefixEnd_1776931 := by exact prefixLift 1776931
  have htrace : WordTrace (prefixWord ++ tailWord_1776931) baseStart_1776931 baseEnd_1776931 := by
    simpa [prefixWord, tailWord_1776931, baseEnd_1776931] using wordTrace_append hprefix tailTrace_1776931
  have hstable : (prefixWord ++ tailWord_1776931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776931).length < 2 ^ (prefixWord ++ tailWord_1776931).sum := by decide
  have hdescent : baseEnd_1776931 < baseStart_1776931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776984 : List Nat := [2, 1, 2, 2, 1, 1, 3, 2, 2, 7]
def baseStart_1776984 : Nat := 118140960795 + 1776984 * 2 ^ 59
def prefixEnd_1776984 : Nat := 4983230072969 + 3 ^ 40 * 1776984 * 2
def baseEnd_1776984 : Nat := 304148969116393591875935

theorem tailTrace_1776984 : CollatzResearch.WordTrace tailWord_1776984 prefixEnd_1776984 304148969116393591875935 := by
  unfold tailWord_1776984
  simp only [CollatzResearch.WordTrace]
  refine ⟨32405965497148963775329003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43207953996198618367105337 32405965497148963775329003)
  ·
    refine ⟨48608948245723445662993505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32405965497148963775329003 48608948245723445662993505)
    ·
      refine ⟨36456711184292584247245129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48608948245723445662993505 36456711184292584247245129)
      ·
        refine ⟨27342533388219438185433847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36456711184292584247245129 27342533388219438185433847)
        ·
          refine ⟨41013800082329157278150771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27342533388219438185433847 41013800082329157278150771)
          ·
            refine ⟨61520700123493735917226157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41013800082329157278150771 61520700123493735917226157)
            ·
              refine ⟨23070262546310150968959809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61520700123493735917226157 23070262546310150968959809)
              ·
                refine ⟨17302696909732613226719857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23070262546310150968959809 17302696909732613226719857)
                ·
                  refine ⟨12977022682299459920039893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17302696909732613226719857 12977022682299459920039893)
                  ·
                    refine ⟨304148969116393591875935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12977022682299459920039893 304148969116393591875935)
                    ·
                      rfl

theorem cell23_1776984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 2, 7].length) (baseStart_1776984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1776984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1776984 prefixEnd_1776984 := by exact prefixLift 1776984
  have htrace : WordTrace (prefixWord ++ tailWord_1776984) baseStart_1776984 baseEnd_1776984 := by
    simpa [prefixWord, tailWord_1776984, baseEnd_1776984] using wordTrace_append hprefix tailTrace_1776984
  have hstable : (prefixWord ++ tailWord_1776984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776984).length < 2 ^ (prefixWord ++ tailWord_1776984).sum := by decide
  have hdescent : baseEnd_1776984 < baseStart_1776984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1776999 : List Nat := [1, 1, 5, 1, 4, 1, 2, 3, 1, 2, 2]
def baseStart_1776999 : Nat := 118140960795 + 1776999 * 2 ^ 59
def prefixEnd_1776999 : Nat := 4983230072969 + 3 ^ 40 * 1776999 * 2
def baseEnd_1776999 : Nat := 912454609558998216940237

theorem tailTrace_1776999 : CollatzResearch.WordTrace tailWord_1776999 prefixEnd_1776999 912454609558998216940237 := by
  unfold tailWord_1776999
  simp only [CollatzResearch.WordTrace]
  refine ⟨64812478089243585112454051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43208318726162390074969367 64812478089243585112454051)
  ·
    refine ⟨97218717133865377668681077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64812478089243585112454051 97218717133865377668681077)
    ·
      refine ⟨9114254731299879156438851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97218717133865377668681077 9114254731299879156438851)
      ·
        refine ⟨13671382096949818734658277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9114254731299879156438851 13671382096949818734658277)
        ·
          refine ⟨2563384143178091012748427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13671382096949818734658277 2563384143178091012748427)
          ·
            refine ⟨3845076214767136519122641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2563384143178091012748427 3845076214767136519122641)
            ·
              refine ⟨2883807161075352389341981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3845076214767136519122641 2883807161075352389341981)
              ·
                refine ⟨1081427685403257146003243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2883807161075352389341981 1081427685403257146003243)
                ·
                  refine ⟨1622141528104885719004865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1081427685403257146003243 1622141528104885719004865)
                  ·
                    refine ⟨1216606146078664289253649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1622141528104885719004865 1216606146078664289253649)
                    ·
                      refine ⟨912454609558998216940237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1216606146078664289253649 912454609558998216940237)
                      ·
                        rfl

theorem cell23_1776999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 3, 1, 2, 2].length) (baseStart_1776999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1776999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1776999 prefixEnd_1776999 := by exact prefixLift 1776999
  have htrace : WordTrace (prefixWord ++ tailWord_1776999) baseStart_1776999 baseEnd_1776999 := by
    simpa [prefixWord, tailWord_1776999, baseEnd_1776999] using wordTrace_append hprefix tailTrace_1776999
  have hstable : (prefixWord ++ tailWord_1776999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1776999).length < 2 ^ (prefixWord ++ tailWord_1776999).sum := by decide
  have hdescent : baseEnd_1776999 < baseStart_1776999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1776999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777031 : List Nat := [1, 1, 4, 2, 2, 2, 2, 1, 2, 6]
def baseStart_1777031 : Nat := 118140960795 + 1777031 * 2 ^ 59
def prefixEnd_1777031 : Nat := 4983230072969 + 3 ^ 40 * 1777031 * 2
def baseEnd_1777031 : Nat := 304157013646647363913363

theorem tailTrace_1777031 : CollatzResearch.WordTrace tailWord_1777031 prefixEnd_1777031 304157013646647363913363 := by
  unfold tailWord_1777031
  simp only [CollatzResearch.WordTrace]
  refine ⟨64813645225127654577618947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43209096816751769718412631 64813645225127654577618947)
  ·
    refine ⟨97220467837691481866428421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64813645225127654577618947 97220467837691481866428421)
    ·
      refine ⟨18228837719567152849955329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97220467837691481866428421 18228837719567152849955329)
      ·
        refine ⟨13671628289675364637466497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18228837719567152849955329 13671628289675364637466497)
        ·
          refine ⟨10253721217256523478099873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13671628289675364637466497 10253721217256523478099873)
          ·
            refine ⟨7690290912942392608574905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10253721217256523478099873 7690290912942392608574905)
            ·
              refine ⟨5767718184706794456431179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7690290912942392608574905 5767718184706794456431179)
              ·
                refine ⟨8651577277060191684646769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5767718184706794456431179 8651577277060191684646769)
                ·
                  refine ⟨6488682957795143763485077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8651577277060191684646769 6488682957795143763485077)
                  ·
                    refine ⟨304157013646647363913363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6488682957795143763485077 304157013646647363913363)
                    ·
                      rfl

theorem cell23_1777031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 2, 6].length) (baseStart_1777031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1777031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1777031 prefixEnd_1777031 := by exact prefixLift 1777031
  have htrace : WordTrace (prefixWord ++ tailWord_1777031) baseStart_1777031 baseEnd_1777031 := by
    simpa [prefixWord, tailWord_1777031, baseEnd_1777031] using wordTrace_append hprefix tailTrace_1777031
  have hstable : (prefixWord ++ tailWord_1777031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777031).length < 2 ^ (prefixWord ++ tailWord_1777031).sum := by decide
  have hdescent : baseEnd_1777031 < baseStart_1777031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777032 : List Nat := [2, 1, 3, 3, 1, 3, 3, 1, 2, 1, 3]
def baseStart_1777032 : Nat := 118140960795 + 1777032 * 2 ^ 59
def prefixEnd_1777032 : Nat := 4983230072969 + 3 ^ 40 * 1777032 * 2
def baseEnd_1777032 : Nat := 912471554420596587827585

theorem tailTrace_1777032 : CollatzResearch.WordTrace tailWord_1777032 prefixEnd_1777032 912471554420596587827585 := by
  unfold tailWord_1777032
  simp only [CollatzResearch.WordTrace]
  refine ⟨32406840849062015874202675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43209121132082687832270233 32406840849062015874202675)
  ·
    refine ⟨48610261273593023811304013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32406840849062015874202675 48610261273593023811304013)
    ·
      refine ⟨18228847977597383929239005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48610261273593023811304013 18228847977597383929239005)
      ·
        refine ⟨6835817991599018973464627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18228847977597383929239005 6835817991599018973464627)
        ·
          refine ⟨10253726987398528460196941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6835817991599018973464627 10253726987398528460196941)
          ·
            refine ⟨3845147620274448172573853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10253726987398528460196941 3845147620274448172573853)
            ·
              refine ⟨1441930357602918064715195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3845147620274448172573853 1441930357602918064715195)
              ·
                refine ⟨2162895536404377097072793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1441930357602918064715195 2162895536404377097072793)
                ·
                  refine ⟨1622171652303282822804595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2162895536404377097072793 1622171652303282822804595)
                  ·
                    refine ⟨2433257478454924234206893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1622171652303282822804595 2433257478454924234206893)
                    ·
                      refine ⟨912471554420596587827585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2433257478454924234206893 912471554420596587827585)
                      ·
                        rfl

theorem cell23_1777032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_1777032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1777032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1777032 prefixEnd_1777032 := by exact prefixLift 1777032
  have htrace : WordTrace (prefixWord ++ tailWord_1777032) baseStart_1777032 baseEnd_1777032 := by
    simpa [prefixWord, tailWord_1777032, baseEnd_1777032] using wordTrace_append hprefix tailTrace_1777032
  have hstable : (prefixWord ++ tailWord_1777032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777032).length < 2 ^ (prefixWord ++ tailWord_1777032).sum := by decide
  have hdescent : baseEnd_1777032 < baseStart_1777032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777055 : List Nat := [1, 1, 2, 5, 1, 2, 1, 2, 4, 2, 2]
def baseStart_1777055 : Nat := 118140960795 + 1777055 * 2 ^ 59
def prefixEnd_1777055 : Nat := 4983230072969 + 3 ^ 40 * 1777055 * 2
def baseEnd_1777055 : Nat := 912483364475649997839979

theorem tailTrace_1777055 : CollatzResearch.WordTrace tailWord_1777055 prefixEnd_1777055 912483364475649997839979 := by
  unfold tailWord_1777055
  simp only [CollatzResearch.WordTrace]
  refine ⟨64814520577040706676492619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43209680384693804450995079 64814520577040706676492619)
  ·
    refine ⟨97221780865561060014738929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64814520577040706676492619 97221780865561060014738929)
    ·
      refine ⟨72916335649170795011054197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97221780865561060014738929 72916335649170795011054197)
      ·
        refine ⟨6835906467109762032286331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72916335649170795011054197 6835906467109762032286331)
        ·
          refine ⟨10253859700664643048429497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6835906467109762032286331 10253859700664643048429497)
          ·
            refine ⟨7690394775498482286322123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10253859700664643048429497 7690394775498482286322123)
            ·
              refine ⟨11535592163247723429483185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7690394775498482286322123 11535592163247723429483185)
              ·
                refine ⟨8651694122435792572112389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11535592163247723429483185 8651694122435792572112389)
                ·
                  refine ⟨1622192647956711107271073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8651694122435792572112389 1622192647956711107271073)
                  ·
                    refine ⟨1216644485967533330453305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1622192647956711107271073 1216644485967533330453305)
                    ·
                      refine ⟨912483364475649997839979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1216644485967533330453305 912483364475649997839979)
                      ·
                        rfl

theorem cell23_1777055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_1777055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1777055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1777055 prefixEnd_1777055 := by exact prefixLift 1777055
  have htrace : WordTrace (prefixWord ++ tailWord_1777055) baseStart_1777055 baseEnd_1777055 := by
    simpa [prefixWord, tailWord_1777055, baseEnd_1777055] using wordTrace_append hprefix tailTrace_1777055
  have hstable : (prefixWord ++ tailWord_1777055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777055).length < 2 ^ (prefixWord ++ tailWord_1777055).sum := by decide
  have hdescent : baseEnd_1777055 < baseStart_1777055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777058 : List Nat := [3, 3, 1, 2, 1, 3, 1, 1, 2, 1, 5]
def baseStart_1777058 : Nat := 118140960795 + 1777058 * 2 ^ 59
def prefixEnd_1777058 : Nat := 4983230072969 + 3 ^ 40 * 1777058 * 2
def baseEnd_1777058 : Nat := 912484904917613486102465

theorem tailTrace_1777058 : CollatzResearch.WordTrace tailWord_1777058 prefixEnd_1777058 912484904917613486102465 := by
  unfold tailWord_1777058
  simp only [CollatzResearch.WordTrace]
  refine ⟨16203657499007459547212957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43209753330686558792567885 16203657499007459547212957)
  ·
    refine ⟨6076371562127797330204859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16203657499007459547212957 6076371562127797330204859)
    ·
      refine ⟨9114557343191695995307289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6076371562127797330204859 9114557343191695995307289)
      ·
        refine ⟨6835918007393771996480467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9114557343191695995307289 6835918007393771996480467)
        ·
          refine ⟨10253877011090657994720701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6835918007393771996480467 10253877011090657994720701)
          ·
            refine ⟨3845203879158996748020263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10253877011090657994720701 3845203879158996748020263)
            ·
              refine ⟨5767805818738495122030395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3845203879158996748020263 5767805818738495122030395)
              ·
                refine ⟨8651708728107742683045593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5767805818738495122030395 8651708728107742683045593)
                ·
                  refine ⟨6488781546080807012284195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8651708728107742683045593 6488781546080807012284195)
                  ·
                    refine ⟨9733172319121210518426293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6488781546080807012284195 9733172319121210518426293)
                    ·
                      refine ⟨912484904917613486102465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9733172319121210518426293 912484904917613486102465)
                      ·
                        rfl

theorem cell23_1777058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_1777058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1777058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1777058 prefixEnd_1777058 := by exact prefixLift 1777058
  have htrace : WordTrace (prefixWord ++ tailWord_1777058) baseStart_1777058 baseEnd_1777058 := by
    simpa [prefixWord, tailWord_1777058, baseEnd_1777058] using wordTrace_append hprefix tailTrace_1777058
  have hstable : (prefixWord ++ tailWord_1777058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777058).length < 2 ^ (prefixWord ++ tailWord_1777058).sum := by decide
  have hdescent : baseEnd_1777058 < baseStart_1777058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777071 : List Nat := [1, 1, 2, 1, 2, 2, 1, 3, 4, 3, 3]
def baseStart_1777071 : Nat := 118140960795 + 1777071 * 2 ^ 59
def prefixEnd_1777071 : Nat := 4983230072969 + 3 ^ 40 * 1777071 * 2
def baseEnd_1777071 : Nat := 912491580166121935239905

theorem tailTrace_1777071 : CollatzResearch.WordTrace tailWord_1777071 prefixEnd_1777071 912491580166121935239905 := by
  unfold tailWord_1777071
  simp only [CollatzResearch.WordTrace]
  refine ⟨64815104144982741409075067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43210069429988494272716711 64815104144982741409075067)
  ·
    refine ⟨97222656217474112113612601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64815104144982741409075067 97222656217474112113612601)
    ·
      refine ⟨72916992163105584085209451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97222656217474112113612601 72916992163105584085209451)
      ·
        refine ⟨109375488244658376127814177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72916992163105584085209451 109375488244658376127814177)
        ·
          refine ⟨82031616183493782095860633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109375488244658376127814177 82031616183493782095860633)
          ·
            refine ⟨61523712137620336571895475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82031616183493782095860633 61523712137620336571895475)
            ·
              refine ⟨92285568206430504857843213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61523712137620336571895475 92285568206430504857843213)
              ·
                refine ⟨34607088077411439321691205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92285568206430504857843213 34607088077411439321691205)
                ·
                  refine ⟨6488829014514644872817101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34607088077411439321691205 6488829014514644872817101)
                  ·
                    refine ⟨2433310880442991827306413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6488829014514644872817101 2433310880442991827306413)
                    ·
                      refine ⟨912491580166121935239905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2433310880442991827306413 912491580166121935239905)
                      ·
                        rfl

theorem cell23_1777071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4, 3, 3].length) (baseStart_1777071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1777071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1777071 prefixEnd_1777071 := by exact prefixLift 1777071
  have htrace : WordTrace (prefixWord ++ tailWord_1777071) baseStart_1777071 baseEnd_1777071 := by
    simpa [prefixWord, tailWord_1777071, baseEnd_1777071] using wordTrace_append hprefix tailTrace_1777071
  have hstable : (prefixWord ++ tailWord_1777071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777071).length < 2 ^ (prefixWord ++ tailWord_1777071).sum := by decide
  have hdescent : baseEnd_1777071 < baseStart_1777071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777111 : List Nat := [1, 1, 3, 2, 1, 1, 1, 5, 1, 3, 4]
def baseStart_1777111 : Nat := 118140960795 + 1777111 * 2 ^ 59
def prefixEnd_1777111 : Nat := 4983230072969 + 3 ^ 40 * 1777111 * 2
def baseEnd_1777111 : Nat := 912512119392301778739721

theorem tailTrace_1777111 : CollatzResearch.WordTrace tailWord_1777111 prefixEnd_1777111 912512119392301778739721 := by
  unfold tailWord_1777111
  simp only [CollatzResearch.WordTrace]
  refine ⟨64816563064837828240531187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43211042043225218827020791 64816563064837828240531187)
  ·
    refine ⟨97224844597256742360796781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64816563064837828240531187 97224844597256742360796781)
    ·
      refine ⟨36459316723971278385298793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97224844597256742360796781 36459316723971278385298793)
      ·
        refine ⟨27344487542978458788974095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36459316723971278385298793 27344487542978458788974095)
        ·
          refine ⟨41016731314467688183461143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27344487542978458788974095 41016731314467688183461143)
          ·
            refine ⟨61525096971701532275191715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41016731314467688183461143 61525096971701532275191715)
            ·
              refine ⟨92287645457552298412787573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61525096971701532275191715 92287645457552298412787573)
              ·
                refine ⟨8651966761645527976198835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92287645457552298412787573 8651966761645527976198835)
                ·
                  refine ⟨12977950142468291964298253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8651966761645527976198835 12977950142468291964298253)
                  ·
                    refine ⟨4866731303425609486611845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12977950142468291964298253 4866731303425609486611845)
                    ·
                      refine ⟨912512119392301778739721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4866731303425609486611845 912512119392301778739721)
                      ·
                        rfl

theorem cell23_1777111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_1777111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1777111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1777111 prefixEnd_1777111 := by exact prefixLift 1777111
  have htrace : WordTrace (prefixWord ++ tailWord_1777111) baseStart_1777111 baseEnd_1777111 := by
    simpa [prefixWord, tailWord_1777111, baseEnd_1777111] using wordTrace_append hprefix tailTrace_1777111
  have hstable : (prefixWord ++ tailWord_1777111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777111).length < 2 ^ (prefixWord ++ tailWord_1777111).sum := by decide
  have hdescent : baseEnd_1777111 < baseStart_1777111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777128 : List Nat := [2, 1, 4, 1, 1, 2, 1, 4, 2, 1, 4]
def baseStart_1777128 : Nat := 118140960795 + 1777128 * 2 ^ 59
def prefixEnd_1777128 : Nat := 4983230072969 + 3 ^ 40 * 1777128 * 2
def baseEnd_1777128 : Nat := 912520848563428212227143

theorem tailTrace_1777128 : CollatzResearch.WordTrace tailWord_1777128 prefixEnd_1777128 912520848563428212227143 := by
  unfold tailWord_1777128
  simp only [CollatzResearch.WordTrace]
  refine ⟨32408591552888120071950019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43211455403850826762600025 32408591552888120071950019)
  ·
    refine ⟨48612887329332180107925029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32408591552888120071950019 48612887329332180107925029)
    ·
      refine ⟨9114916374249783770235943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48612887329332180107925029 9114916374249783770235943)
      ·
        refine ⟨13672374561374675655353915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9114916374249783770235943 13672374561374675655353915)
        ·
          refine ⟨20508561842062013483030873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13672374561374675655353915 20508561842062013483030873)
          ·
            refine ⟨15381421381546510112273155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20508561842062013483030873 15381421381546510112273155)
            ·
              refine ⟨23072132072319765168409733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15381421381546510112273155 23072132072319765168409733)
              ·
                refine ⟨4326024763559955969076825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23072132072319765168409733 4326024763559955969076825)
                ·
                  refine ⟨3244518572669966976807619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4326024763559955969076825 3244518572669966976807619)
                  ·
                    refine ⟨4866777859004950465211429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3244518572669966976807619 4866777859004950465211429)
                    ·
                      refine ⟨912520848563428212227143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4866777859004950465211429 912520848563428212227143)
                      ·
                        rfl

theorem cell23_1777128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_1777128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1777128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1777128 prefixEnd_1777128 := by exact prefixLift 1777128
  have htrace : WordTrace (prefixWord ++ tailWord_1777128) baseStart_1777128 baseEnd_1777128 := by
    simpa [prefixWord, tailWord_1777128, baseEnd_1777128] using wordTrace_append hprefix tailTrace_1777128
  have hstable : (prefixWord ++ tailWord_1777128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777128).length < 2 ^ (prefixWord ++ tailWord_1777128).sum := by decide
  have hdescent : baseEnd_1777128 < baseStart_1777128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777148 : List Nat := [2, 2, 2, 1, 2, 1, 2, 2, 4, 2, 3]
def baseStart_1777148 : Nat := 118140960795 + 1777148 * 2 ^ 59
def prefixEnd_1777148 : Nat := 4983230072969 + 3 ^ 40 * 1777148 * 2
def baseEnd_1777148 : Nat := 912531118176518133977051

theorem tailTrace_1777148 : CollatzResearch.WordTrace tailWord_1777148 prefixEnd_1777148 912531118176518133977051 := by
  unfold tailWord_1777148
  simp only [CollatzResearch.WordTrace]
  refine ⟨32408956282851891779814049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43211941710469189039752065 32408956282851891779814049)
  ·
    refine ⟨24306717212138918834860537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32408956282851891779814049 24306717212138918834860537)
    ·
      refine ⟨18230037909104189126145403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24306717212138918834860537 18230037909104189126145403)
      ·
        refine ⟨27345056863656283689218105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18230037909104189126145403 27345056863656283689218105)
        ·
          refine ⟨20508792647742212766913579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27345056863656283689218105 20508792647742212766913579)
          ·
            refine ⟨30763188971613319150370369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20508792647742212766913579 30763188971613319150370369)
            ·
              refine ⟨23072391728709989362777777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30763188971613319150370369 23072391728709989362777777)
              ·
                refine ⟨17304293796532492022083333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23072391728709989362777777 17304293796532492022083333)
                ·
                  refine ⟨3244555086849842254140625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17304293796532492022083333 3244555086849842254140625)
                  ·
                    refine ⟨2433416315137381690605469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3244555086849842254140625 2433416315137381690605469)
                    ·
                      refine ⟨912531118176518133977051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2433416315137381690605469 912531118176518133977051)
                      ·
                        rfl

theorem cell23_1777148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 4, 2, 3].length) (baseStart_1777148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1777148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1777148 prefixEnd_1777148 := by exact prefixLift 1777148
  have htrace : WordTrace (prefixWord ++ tailWord_1777148) baseStart_1777148 baseEnd_1777148 := by
    simpa [prefixWord, tailWord_1777148, baseEnd_1777148] using wordTrace_append hprefix tailTrace_1777148
  have hstable : (prefixWord ++ tailWord_1777148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777148).length < 2 ^ (prefixWord ++ tailWord_1777148).sum := by decide
  have hdescent : baseEnd_1777148 < baseStart_1777148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777185 : List Nat := [1, 2, 3, 2, 2, 4, 1, 2, 6]
def baseStart_1777185 : Nat := 118140960795 + 1777185 * 2 ^ 59
def prefixEnd_1777185 : Nat := 4983230072969 + 3 ^ 40 * 1777185 * 2
def baseEnd_1777185 : Nat := 101394457440081609912709

theorem tailTrace_1777185 : CollatzResearch.WordTrace tailWord_1777185 prefixEnd_1777185 101394457440081609912709 := by
  unfold tailWord_1777185
  simp only [CollatzResearch.WordTrace]
  refine ⟨64819262066569738878725009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43212841377713159252483339 64819262066569738878725009)
  ·
    refine ⟨48614446549927304159043757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64819262066569738878725009 48614446549927304159043757)
    ·
      refine ⟨18230417456222739059641409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48614446549927304159043757 18230417456222739059641409)
      ·
        refine ⟨13672813092167054294731057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18230417456222739059641409 13672813092167054294731057)
        ·
          refine ⟨10254609819125290721048293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13672813092167054294731057 10254609819125290721048293)
          ·
            refine ⟨1922739341085992010196555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10254609819125290721048293 1922739341085992010196555)
            ·
              refine ⟨2884109011628988015294833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1922739341085992010196555 2884109011628988015294833)
              ·
                refine ⟨2163081758721741011471125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2884109011628988015294833 2163081758721741011471125)
                ·
                  refine ⟨101394457440081609912709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2163081758721741011471125 101394457440081609912709)
                  ·
                    rfl

theorem cell23_1777185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 2, 6].length) (baseStart_1777185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1777185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1777185 prefixEnd_1777185 := by exact prefixLift 1777185
  have htrace : WordTrace (prefixWord ++ tailWord_1777185) baseStart_1777185 baseEnd_1777185 := by
    simpa [prefixWord, tailWord_1777185, baseEnd_1777185] using wordTrace_append hprefix tailTrace_1777185
  have hstable : (prefixWord ++ tailWord_1777185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777185).length < 2 ^ (prefixWord ++ tailWord_1777185).sum := by decide
  have hdescent : baseEnd_1777185 < baseStart_1777185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777205 : List Nat := [1, 3, 3, 1, 1, 3, 1, 2, 1, 5, 2]
def baseStart_1777205 : Nat := 118140960795 + 1777205 * 2 ^ 59
def prefixEnd_1777205 : Nat := 4983230072969 + 3 ^ 40 * 1777205 * 2
def baseEnd_1777205 : Nat := 912560386573824410964289

theorem tailTrace_1777205 : CollatzResearch.WordTrace tailWord_1777205 prefixEnd_1777205 912560386573824410964289 := by
  unfold tailWord_1777205
  simp only [CollatzResearch.WordTrace]
  refine ⟨64819991526497282294453069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43213327684331521529635379 64819991526497282294453069)
  ·
    refine ⟨24307496822436480860419901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64819991526497282294453069 24307496822436480860419901)
    ·
      refine ⟨9115311308413680322657463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24307496822436480860419901 9115311308413680322657463)
      ·
        refine ⟨13672966962620520483986195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9115311308413680322657463 13672966962620520483986195)
        ·
          refine ⟨20509450443930780725979293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13672966962620520483986195 20509450443930780725979293)
          ·
            refine ⟨7691043916474042772242235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20509450443930780725979293 7691043916474042772242235)
            ·
              refine ⟨11536565874711064158363353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7691043916474042772242235 11536565874711064158363353)
              ·
                refine ⟨8652424406033298118772515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11536565874711064158363353 8652424406033298118772515)
                ·
                  refine ⟨12978636609049947178158773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8652424406033298118772515 12978636609049947178158773)
                  ·
                    refine ⟨1216747182098432547952385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12978636609049947178158773 1216747182098432547952385)
                    ·
                      refine ⟨912560386573824410964289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1216747182098432547952385 912560386573824410964289)
                      ·
                        rfl

theorem cell23_1777205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 5, 2].length) (baseStart_1777205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1777205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1777205 prefixEnd_1777205 := by exact prefixLift 1777205
  have htrace : WordTrace (prefixWord ++ tailWord_1777205) baseStart_1777205 baseEnd_1777205 := by
    simpa [prefixWord, tailWord_1777205, baseEnd_1777205] using wordTrace_append hprefix tailTrace_1777205
  have hstable : (prefixWord ++ tailWord_1777205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777205).length < 2 ^ (prefixWord ++ tailWord_1777205).sum := by decide
  have hdescent : baseEnd_1777205 < baseStart_1777205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777215 : List Nat := [1, 1, 2, 2, 3, 4, 2, 2, 1, 5]
def baseStart_1777215 : Nat := 118140960795 + 1777215 * 2 ^ 59
def prefixEnd_1777215 : Nat := 4983230072969 + 3 ^ 40 * 1777215 * 2
def baseEnd_1777215 : Nat := 304188507126789790613081

theorem tailTrace_1777215 : CollatzResearch.WordTrace tailWord_1777215 prefixEnd_1777215 304188507126789790613081 := by
  unfold tailWord_1777215
  simp only [CollatzResearch.WordTrace]
  refine ⟨64820356256461054002317099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43213570837640702668211399 64820356256461054002317099)
  ·
    refine ⟨97230534384691581003475649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64820356256461054002317099 97230534384691581003475649)
    ·
      refine ⟨72922900788518685752606737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97230534384691581003475649 72922900788518685752606737)
      ·
        refine ⟨54692175591389014314455053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72922900788518685752606737 54692175591389014314455053)
        ·
          refine ⟨20509565846770880367920645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54692175591389014314455053 20509565846770880367920645)
          ·
            refine ⟨3845543596269540068985121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20509565846770880367920645 3845543596269540068985121)
            ·
              refine ⟨2884157697202155051738841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3845543596269540068985121 2884157697202155051738841)
              ·
                refine ⟨2163118272901616288804131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2884157697202155051738841 2163118272901616288804131)
                ·
                  refine ⟨3244677409352424433206197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2163118272901616288804131 3244677409352424433206197)
                  ·
                    refine ⟨304188507126789790613081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3244677409352424433206197 304188507126789790613081)
                    ·
                      rfl

theorem cell23_1777215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 2, 1, 5].length) (baseStart_1777215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1777215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1777215 prefixEnd_1777215 := by exact prefixLift 1777215
  have htrace : WordTrace (prefixWord ++ tailWord_1777215) baseStart_1777215 baseEnd_1777215 := by
    simpa [prefixWord, tailWord_1777215, baseEnd_1777215] using wordTrace_append hprefix tailTrace_1777215
  have hstable : (prefixWord ++ tailWord_1777215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777215).length < 2 ^ (prefixWord ++ tailWord_1777215).sum := by decide
  have hdescent : baseEnd_1777215 < baseStart_1777215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777258 : List Nat := [3, 1, 3, 2, 1, 2, 1, 10]
def baseStart_1777258 : Nat := 118140960795 + 1777258 * 2 ^ 59
def prefixEnd_1777258 : Nat := 4983230072969 + 3 ^ 40 * 1777258 * 2
def baseEnd_1777258 : Nat := 33799540779574544577835

theorem tailTrace_1777258 : CollatzResearch.WordTrace tailWord_1777258 prefixEnd_1777258 33799540779574544577835 := by
  unfold tailWord_1777258
  simp only [CollatzResearch.WordTrace]
  refine ⟨16205481148826318086533107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43214616396870181564088285 16205481148826318086533107)
  ·
    refine ⟨24308221723239477129799661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16205481148826318086533107 24308221723239477129799661)
    ·
      refine ⟨9115583146214803923674873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24308221723239477129799661 9115583146214803923674873)
      ·
        refine ⟨6836687359661102942756155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9115583146214803923674873 6836687359661102942756155)
        ·
          refine ⟨10255031039491654414134233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6836687359661102942756155 10255031039491654414134233)
          ·
            refine ⟨7691273279618740810600675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10255031039491654414134233 7691273279618740810600675)
            ·
              refine ⟨11536909919428111215901013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7691273279618740810600675 11536909919428111215901013)
              ·
                refine ⟨33799540779574544577835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 11536909919428111215901013 33799540779574544577835)
                ·
                  rfl

theorem cell23_1777258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 10].length) (baseStart_1777258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1777258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1777258 prefixEnd_1777258 := by exact prefixLift 1777258
  have htrace : WordTrace (prefixWord ++ tailWord_1777258) baseStart_1777258 baseEnd_1777258 := by
    simpa [prefixWord, tailWord_1777258, baseEnd_1777258] using wordTrace_append hprefix tailTrace_1777258
  have hstable : (prefixWord ++ tailWord_1777258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777258).length < 2 ^ (prefixWord ++ tailWord_1777258).sum := by decide
  have hdescent : baseEnd_1777258 < baseStart_1777258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777269 : List Nat := [1, 3, 4, 2, 1, 3, 1, 2, 1, 1, 4]
def baseStart_1777269 : Nat := 118140960795 + 1777269 * 2 ^ 59
def prefixEnd_1777269 : Nat := 4983230072969 + 3 ^ 40 * 1777269 * 2
def baseEnd_1777269 : Nat := 912593249335712160563995

theorem tailTrace_1777269 : CollatzResearch.WordTrace tailWord_1777269 prefixEnd_1777269 912593249335712160563995 := by
  unfold tailWord_1777269
  simp only [CollatzResearch.WordTrace]
  refine ⟨64822325798265421224782861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43214883865510280816521907 64822325798265421224782861)
  ·
    refine ⟨24308372174349532959293573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64822325798265421224782861 24308372174349532959293573)
    ·
      refine ⟨4557819782690537429867545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24308372174349532959293573 4557819782690537429867545)
      ·
        refine ⟨3418364837017903072400659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4557819782690537429867545 3418364837017903072400659)
        ·
          refine ⟨5127547255526854608600989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3418364837017903072400659 5127547255526854608600989)
          ·
            refine ⟨1922830220822570478225371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5127547255526854608600989 1922830220822570478225371)
            ·
              refine ⟨2884245331233855717338057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1922830220822570478225371 2884245331233855717338057)
              ·
                refine ⟨2163183998425391788003543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2884245331233855717338057 2163183998425391788003543)
                ·
                  refine ⟨3244775997638087682005315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2163183998425391788003543 3244775997638087682005315)
                  ·
                    refine ⟨4867163996457131523007973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3244775997638087682005315 4867163996457131523007973)
                    ·
                      refine ⟨912593249335712160563995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4867163996457131523007973 912593249335712160563995)
                      ·
                        rfl

theorem cell23_1777269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_1777269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1777269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1777269 prefixEnd_1777269 := by exact prefixLift 1777269
  have htrace : WordTrace (prefixWord ++ tailWord_1777269) baseStart_1777269 baseEnd_1777269 := by
    simpa [prefixWord, tailWord_1777269, baseEnd_1777269] using wordTrace_append hprefix tailTrace_1777269
  have hstable : (prefixWord ++ tailWord_1777269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777269).length < 2 ^ (prefixWord ++ tailWord_1777269).sum := by decide
  have hdescent : baseEnd_1777269 < baseStart_1777269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777285 : List Nat := [1, 3, 1, 1, 4, 1, 3, 2, 1, 3, 3]
def baseStart_1777285 : Nat := 118140960795 + 1777285 * 2 ^ 59
def prefixEnd_1777285 : Nat := 4983230072969 + 3 ^ 40 * 1777285 * 2
def baseEnd_1777285 : Nat := 912601465026184097963921

theorem tailTrace_1777285 : CollatzResearch.WordTrace tailWord_1777285 prefixEnd_1777285 912601465026184097963921 := by
  unfold tailWord_1777285
  simp only [CollatzResearch.WordTrace]
  refine ⟨64822909366207455957365309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43215272910804970638243539 64822909366207455957365309)
  ·
    refine ⟨24308591012327795984011991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64822909366207455957365309 24308591012327795984011991)
    ·
      refine ⟨36462886518491693976017987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24308591012327795984011991 36462886518491693976017987)
      ·
        refine ⟨54694329777737540964026981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36462886518491693976017987 54694329777737540964026981)
        ·
          refine ⟨10255186833325788930755059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54694329777737540964026981 10255186833325788930755059)
          ·
            refine ⟨15382780249988683396132589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10255186833325788930755059 15382780249988683396132589)
            ·
              refine ⟨5768542593745756273549721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15382780249988683396132589 5768542593745756273549721)
              ·
                refine ⟨4326406945309317205162291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5768542593745756273549721 4326406945309317205162291)
                ·
                  refine ⟨6489610417963975807743437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4326406945309317205162291 6489610417963975807743437)
                  ·
                    refine ⟨2433603906736490927903789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6489610417963975807743437 2433603906736490927903789)
                    ·
                      refine ⟨912601465026184097963921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2433603906736490927903789 912601465026184097963921)
                      ·
                        rfl

theorem cell23_1777285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2, 1, 3, 3].length) (baseStart_1777285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1777285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1777285 prefixEnd_1777285 := by exact prefixLift 1777285
  have htrace : WordTrace (prefixWord ++ tailWord_1777285) baseStart_1777285 baseEnd_1777285 := by
    simpa [prefixWord, tailWord_1777285, baseEnd_1777285] using wordTrace_append hprefix tailTrace_1777285
  have hstable : (prefixWord ++ tailWord_1777285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777285).length < 2 ^ (prefixWord ++ tailWord_1777285).sum := by decide
  have hdescent : baseEnd_1777285 < baseStart_1777285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777295 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 7, 3, 2]
def baseStart_1777295 : Nat := 118140960795 + 1777295 * 2 ^ 59
def prefixEnd_1777295 : Nat := 4983230072969 + 3 ^ 40 * 1777295 * 2
def baseEnd_1777295 : Nat := 912606599832729058838875

theorem tailTrace_1777295 : CollatzResearch.WordTrace tailWord_1777295 prefixEnd_1777295 912606599832729058838875 := by
  unfold tailWord_1777295
  simp only [CollatzResearch.WordTrace]
  refine ⟨64823274096171227665229339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43215516064114151776819559 64823274096171227665229339)
  ·
    refine ⟨97234911144256841497844009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64823274096171227665229339 97234911144256841497844009)
    ·
      refine ⟨72926183358192631123383007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97234911144256841497844009 72926183358192631123383007)
      ·
        refine ⟨109389275037288946685074511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72926183358192631123383007 109389275037288946685074511)
        ·
          refine ⟨164083912555933420027611767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109389275037288946685074511 164083912555933420027611767)
          ·
            refine ⟨246125868833900130041417651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164083912555933420027611767 246125868833900130041417651)
            ·
              refine ⟨369188803250850195062126477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246125868833900130041417651 369188803250850195062126477)
              ·
                refine ⟨138445801219068823148297429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 369188803250850195062126477 138445801219068823148297429)
                ·
                  refine ⟨3244823466071925542538221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 138445801219068823148297429 3244823466071925542538221)
                  ·
                    refine ⟨1216808799776972078451833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3244823466071925542538221 1216808799776972078451833)
                    ·
                      refine ⟨912606599832729058838875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1216808799776972078451833 912606599832729058838875)
                      ·
                        rfl

theorem cell23_1777295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 7, 3, 2].length) (baseStart_1777295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1777295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1777295 prefixEnd_1777295 := by exact prefixLift 1777295
  have htrace : WordTrace (prefixWord ++ tailWord_1777295) baseStart_1777295 baseEnd_1777295 := by
    simpa [prefixWord, tailWord_1777295, baseEnd_1777295] using wordTrace_append hprefix tailTrace_1777295
  have hstable : (prefixWord ++ tailWord_1777295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777295).length < 2 ^ (prefixWord ++ tailWord_1777295).sum := by decide
  have hdescent : baseEnd_1777295 < baseStart_1777295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777303 : List Nat := [1, 1, 3, 3, 2, 4, 2, 2, 1, 2, 2]
def baseStart_1777303 : Nat := 118140960795 + 1777303 * 2 ^ 59
def prefixEnd_1777303 : Nat := 4983230072969 + 3 ^ 40 * 1777303 * 2
def baseEnd_1777303 : Nat := 912610707677965027538839

theorem tailTrace_1777303 : CollatzResearch.WordTrace tailWord_1777303 prefixEnd_1777303 912610707677965027538839 := by
  unfold tailWord_1777303
  simp only [CollatzResearch.WordTrace]
  refine ⟨64823565880142245031520563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43215710586761496687680375 64823565880142245031520563)
  ·
    refine ⟨97235348820213367547280845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64823565880142245031520563 97235348820213367547280845)
    ·
      refine ⟨36463255807580012830230317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97235348820213367547280845 36463255807580012830230317)
      ·
        refine ⟨13673720927842504811336369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36463255807580012830230317 13673720927842504811336369)
        ·
          refine ⟨10255290695881878608502277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13673720927842504811336369 10255290695881878608502277)
          ·
            refine ⟨1922867005477852239094177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10255290695881878608502277 1922867005477852239094177)
            ·
              refine ⟨1442150254108389179320633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1922867005477852239094177 1442150254108389179320633)
              ·
                refine ⟨1081612690581291884490475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1442150254108389179320633 1081612690581291884490475)
                ·
                  refine ⟨1622419035871937826735713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1081612690581291884490475 1622419035871937826735713)
                  ·
                    refine ⟨1216814276903953370051785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1622419035871937826735713 1216814276903953370051785)
                    ·
                      refine ⟨912610707677965027538839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1216814276903953370051785 912610707677965027538839)
                      ·
                        rfl

theorem cell23_1777303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 2, 1, 2, 2].length) (baseStart_1777303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1777303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1777303 prefixEnd_1777303 := by exact prefixLift 1777303
  have htrace : WordTrace (prefixWord ++ tailWord_1777303) baseStart_1777303 baseEnd_1777303 := by
    simpa [prefixWord, tailWord_1777303, baseEnd_1777303] using wordTrace_append hprefix tailTrace_1777303
  have hstable : (prefixWord ++ tailWord_1777303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777303).length < 2 ^ (prefixWord ++ tailWord_1777303).sum := by decide
  have hdescent : baseEnd_1777303 < baseStart_1777303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777312 : List Nat := [2, 1, 1, 4, 3, 1, 1, 2, 3, 3, 2]
def baseStart_1777312 : Nat := 118140960795 + 1777312 * 2 ^ 59
def prefixEnd_1777312 : Nat := 4983230072969 + 3 ^ 40 * 1777312 * 2
def baseEnd_1777312 : Nat := 912615329003855492326297

theorem tailTrace_1777312 : CollatzResearch.WordTrace tailWord_1777312 prefixEnd_1777312 912615329003855492326297 := by
  unfold tailWord_1777312
  simp only [CollatzResearch.WordTrace]
  refine ⟨32411947068554819784299095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43215929424739759712398793 32411947068554819784299095)
  ·
    refine ⟨48617920602832229676448643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32411947068554819784299095 48617920602832229676448643)
    ·
      refine ⟨72926880904248344514672965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48617920602832229676448643 72926880904248344514672965)
      ·
        refine ⟨13673790169546564596501181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72926880904248344514672965 13673790169546564596501181)
        ·
          refine ⟨5127671313579961723687943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13673790169546564596501181 5127671313579961723687943)
          ·
            refine ⟨7691506970369942585531915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5127671313579961723687943 7691506970369942585531915)
            ·
              refine ⟨11537260455554913878297873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7691506970369942585531915 11537260455554913878297873)
              ·
                refine ⟨8652945341666185408723405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11537260455554913878297873 8652945341666185408723405)
                ·
                  refine ⟨3244854503124819528271277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8652945341666185408723405 3244854503124819528271277)
                  ·
                    refine ⟨1216820438671807323101729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3244854503124819528271277 1216820438671807323101729)
                    ·
                      refine ⟨912615329003855492326297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1216820438671807323101729 912615329003855492326297)
                      ·
                        rfl

theorem cell23_1777312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 3, 3, 2].length) (baseStart_1777312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1777312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1777312 prefixEnd_1777312 := by exact prefixLift 1777312
  have htrace : WordTrace (prefixWord ++ tailWord_1777312) baseStart_1777312 baseEnd_1777312 := by
    simpa [prefixWord, tailWord_1777312, baseEnd_1777312] using wordTrace_append hprefix tailTrace_1777312
  have hstable : (prefixWord ++ tailWord_1777312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777312).length < 2 ^ (prefixWord ++ tailWord_1777312).sum := by decide
  have hdescent : baseEnd_1777312 < baseStart_1777312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777325 : List Nat := [1, 5, 2, 1, 1, 1, 1, 2, 2, 3, 4]
def baseStart_1777325 : Nat := 118140960795 + 1777325 * 2 ^ 59
def prefixEnd_1777325 : Nat := 4983230072969 + 3 ^ 40 * 1777325 * 2
def baseEnd_1777325 : Nat := 912622004252363941463737

theorem tailTrace_1777325 : CollatzResearch.WordTrace tailWord_1777325 prefixEnd_1777325 912622004252363941463737 := by
  unfold tailWord_1777325
  simp only [CollatzResearch.WordTrace]
  refine ⟨64824368286062542788821429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43216245524041695192547619 64824368286062542788821429)
  ·
    refine ⟨6077284526818363386452009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64824368286062542788821429 6077284526818363386452009)
    ·
      refine ⟨4557963395113772539839007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6077284526818363386452009 4557963395113772539839007)
      ·
        refine ⟨6836945092670658809758511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4557963395113772539839007 6836945092670658809758511)
        ·
          refine ⟨10255417639005988214637767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6836945092670658809758511 10255417639005988214637767)
          ·
            refine ⟨15383126458508982321956651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10255417639005988214637767 15383126458508982321956651)
            ·
              refine ⟨23074689687763473482934977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15383126458508982321956651 23074689687763473482934977)
              ·
                refine ⟨17306017265822605112201233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23074689687763473482934977 17306017265822605112201233)
                ·
                  refine ⟨12979512949366953834150925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17306017265822605112201233 12979512949366953834150925)
                  ·
                    refine ⟨4867317356012607687806597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12979512949366953834150925 4867317356012607687806597)
                    ·
                      refine ⟨912622004252363941463737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4867317356012607687806597 912622004252363941463737)
                      ·
                        rfl

theorem cell23_1777325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_1777325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1777325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1777325 prefixEnd_1777325 := by exact prefixLift 1777325
  have htrace : WordTrace (prefixWord ++ tailWord_1777325) baseStart_1777325 baseEnd_1777325 := by
    simpa [prefixWord, tailWord_1777325, baseEnd_1777325] using wordTrace_append hprefix tailTrace_1777325
  have hstable : (prefixWord ++ tailWord_1777325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777325).length < 2 ^ (prefixWord ++ tailWord_1777325).sum := by decide
  have hdescent : baseEnd_1777325 < baseStart_1777325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777328 : List Nat := [2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 5]
def baseStart_1777328 : Nat := 118140960795 + 1777328 * 2 ^ 59
def prefixEnd_1777328 : Nat := 4983230072969 + 3 ^ 40 * 1777328 * 2
def baseEnd_1777328 : Nat := 912623544694327429726223

theorem tailTrace_1777328 : CollatzResearch.WordTrace tailWord_1777328 prefixEnd_1777328 912623544694327429726223 := by
  unfold tailWord_1777328
  simp only [CollatzResearch.WordTrace]
  refine ⟨32412238852525837150590319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43216318470034449534120425 32412238852525837150590319)
  ·
    refine ⟨48618358278788755725885479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32412238852525837150590319 48618358278788755725885479)
    ·
      refine ⟨72927537418183133588828219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48618358278788755725885479 72927537418183133588828219)
      ·
        refine ⟨109391306127274700383242329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72927537418183133588828219 109391306127274700383242329)
        ·
          refine ⟨82043479595456025287431747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109391306127274700383242329 82043479595456025287431747)
          ·
            refine ⟨123065219393184037931147621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82043479595456025287431747 123065219393184037931147621)
            ·
              refine ⟨23074728636222007112090179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123065219393184037931147621 23074728636222007112090179)
              ·
                refine ⟨34612092954333010668135269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23074728636222007112090179 34612092954333010668135269)
                ·
                  refine ⟨6489767428937439500275363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34612092954333010668135269 6489767428937439500275363)
                  ·
                    refine ⟨9734651143406159250413045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6489767428937439500275363 9734651143406159250413045)
                    ·
                      refine ⟨912623544694327429726223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9734651143406159250413045 912623544694327429726223)
                      ·
                        rfl

theorem cell23_1777328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 5].length) (baseStart_1777328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1777328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1777328 prefixEnd_1777328 := by exact prefixLift 1777328
  have htrace : WordTrace (prefixWord ++ tailWord_1777328) baseStart_1777328 baseEnd_1777328 := by
    simpa [prefixWord, tailWord_1777328, baseEnd_1777328] using wordTrace_append hprefix tailTrace_1777328
  have hstable : (prefixWord ++ tailWord_1777328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777328).length < 2 ^ (prefixWord ++ tailWord_1777328).sum := by decide
  have hdescent : baseEnd_1777328 < baseStart_1777328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777375 : List Nat := [1, 1, 2, 3, 2, 2, 1, 3, 2, 3, 3]
def baseStart_1777375 : Nat := 118140960795 + 1777375 * 2 ^ 59
def prefixEnd_1777375 : Nat := 4983230072969 + 3 ^ 40 * 1777375 * 2
def baseEnd_1777375 : Nat := 912647678285088745838507

theorem tailTrace_1777375 : CollatzResearch.WordTrace tailWord_1777375 prefixEnd_1777375 912647678285088745838507 := by
  unfold tailWord_1777375
  simp only [CollatzResearch.WordTrace]
  refine ⟨64826191935881401328141579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43217461290587600885427719 64826191935881401328141579)
  ·
    refine ⟨97239287903822101992212369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64826191935881401328141579 97239287903822101992212369)
    ·
      refine ⟨72929465927866576494159277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97239287903822101992212369 72929465927866576494159277)
      ·
        refine ⟨27348549722949966185309729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72929465927866576494159277 27348549722949966185309729)
        ·
          refine ⟨20511412292212474638982297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27348549722949966185309729 20511412292212474638982297)
          ·
            refine ⟨15383559219159355979236723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20511412292212474638982297 15383559219159355979236723)
            ·
              refine ⟨23075338828739033968855085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15383559219159355979236723 23075338828739033968855085)
              ·
                refine ⟨8653252060777137738320657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23075338828739033968855085 8653252060777137738320657)
                ·
                  refine ⟨6489939045582853303740493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8653252060777137738320657 6489939045582853303740493)
                  ·
                    refine ⟨2433727142093569988902685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6489939045582853303740493 2433727142093569988902685)
                    ·
                      refine ⟨912647678285088745838507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2433727142093569988902685 912647678285088745838507)
                      ·
                        rfl

theorem cell23_1777375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2, 3, 3].length) (baseStart_1777375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1777375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1777375 prefixEnd_1777375 := by exact prefixLift 1777375
  have htrace : WordTrace (prefixWord ++ tailWord_1777375) baseStart_1777375 baseEnd_1777375 := by
    simpa [prefixWord, tailWord_1777375, baseEnd_1777375] using wordTrace_append hprefix tailTrace_1777375
  have hstable : (prefixWord ++ tailWord_1777375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777375).length < 2 ^ (prefixWord ++ tailWord_1777375).sum := by decide
  have hdescent : baseEnd_1777375 < baseStart_1777375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777408 : List Nat := [2, 1, 1, 2, 1, 1, 2, 2, 1, 10]
def baseStart_1777408 : Nat := 118140960795 + 1777408 * 2 ^ 59
def prefixEnd_1777408 : Nat := 4983230072969 + 3 ^ 40 * 1777408 * 2
def baseEnd_1777408 : Nat := 304221541048895705575285

theorem tailTrace_1777408 : CollatzResearch.WordTrace tailWord_1777408 prefixEnd_1777408 304221541048895705575285 := by
  unfold tailWord_1777408
  simp only [CollatzResearch.WordTrace]
  refine ⟨32413697772380923982046439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43218263696507898642728585 32413697772380923982046439)
  ·
    refine ⟨48620546658571385973069659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32413697772380923982046439 48620546658571385973069659)
    ·
      refine ⟨72930819987857078959604489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48620546658571385973069659 72930819987857078959604489)
      ·
        refine ⟨54698114990892809219703367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72930819987857078959604489 54698114990892809219703367)
        ·
          refine ⟨82047172486339213829555051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54698114990892809219703367 82047172486339213829555051)
          ·
            refine ⟨123070758729508820744332577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82047172486339213829555051 123070758729508820744332577)
            ·
              refine ⟨92303069047131615558249433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123070758729508820744332577 92303069047131615558249433)
              ·
                refine ⟨69227301785348711668687075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92303069047131615558249433 69227301785348711668687075)
                ·
                  refine ⟨103840952678023067503030613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69227301785348711668687075 103840952678023067503030613)
                  ·
                    refine ⟨304221541048895705575285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 103840952678023067503030613 304221541048895705575285)
                    ·
                      rfl

theorem cell23_1777408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 1, 10].length) (baseStart_1777408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1777408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1777408 prefixEnd_1777408 := by exact prefixLift 1777408
  have htrace : WordTrace (prefixWord ++ tailWord_1777408) baseStart_1777408 baseEnd_1777408 := by
    simpa [prefixWord, tailWord_1777408, baseEnd_1777408] using wordTrace_append hprefix tailTrace_1777408
  have hstable : (prefixWord ++ tailWord_1777408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777408).length < 2 ^ (prefixWord ++ tailWord_1777408).sum := by decide
  have hdescent : baseEnd_1777408 < baseStart_1777408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777412 : List Nat := [2, 3, 2, 2, 1, 3, 1, 2, 2, 5]
def baseStart_1777412 : Nat := 118140960795 + 1777412 * 2 ^ 59
def prefixEnd_1777412 : Nat := 4983230072969 + 3 ^ 40 * 1777412 * 2
def baseEnd_1777412 : Nat := 304222225689768367025279

theorem tailTrace_1777412 : CollatzResearch.WordTrace tailWord_1777412 prefixEnd_1777412 304222225689768367025279 := by
  unfold tailWord_1777412
  simp only [CollatzResearch.WordTrace]
  refine ⟨32413770718373678323619245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43218360957831571098158993 32413770718373678323619245)
  ·
    refine ⟨12155164019390129371357217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32413770718373678323619245 12155164019390129371357217)
    ·
      refine ⟨9116373014542597028517913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12155164019390129371357217 9116373014542597028517913)
      ·
        refine ⟨6837279760906947771388435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9116373014542597028517913 6837279760906947771388435)
        ·
          refine ⟨10255919641360421657082653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6837279760906947771388435 10255919641360421657082653)
          ·
            refine ⟨3845969865510158121405995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10255919641360421657082653 3845969865510158121405995)
            ·
              refine ⟨5768954798265237182108993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3845969865510158121405995 5768954798265237182108993)
              ·
                refine ⟨4326716098698927886581745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5768954798265237182108993 4326716098698927886581745)
                ·
                  refine ⟨3245037074024195914936309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4326716098698927886581745 3245037074024195914936309)
                  ·
                    refine ⟨304222225689768367025279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3245037074024195914936309 304222225689768367025279)
                    ·
                      rfl

theorem cell23_1777412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_1777412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1777412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1777412 prefixEnd_1777412 := by exact prefixLift 1777412
  have htrace : WordTrace (prefixWord ++ tailWord_1777412) baseStart_1777412 baseEnd_1777412 := by
    simpa [prefixWord, tailWord_1777412, baseEnd_1777412] using wordTrace_append hprefix tailTrace_1777412
  have hstable : (prefixWord ++ tailWord_1777412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777412).length < 2 ^ (prefixWord ++ tailWord_1777412).sum := by decide
  have hdescent : baseEnd_1777412 < baseStart_1777412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777432 : List Nat := [2, 1, 2, 3, 1, 1, 2, 3, 2, 4, 2]
def baseStart_1777432 : Nat := 118140960795 + 1777432 * 2 ^ 59
def prefixEnd_1777432 : Nat := 4983230072969 + 3 ^ 40 * 1777432 * 2
def baseEnd_1777432 : Nat := 912676946682395022825745

theorem tailTrace_1777432 : CollatzResearch.WordTrace tailWord_1777432 prefixEnd_1777432 912676946682395022825745 := by
  unfold tailWord_1777432
  simp only [CollatzResearch.WordTrace]
  refine ⟨32414135448337450031483275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43218847264449933375311033 32414135448337450031483275)
  ·
    refine ⟨48621203172506175047224913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32414135448337450031483275 48621203172506175047224913)
    ·
      refine ⟨36465902379379631285418685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48621203172506175047224913 36465902379379631285418685)
      ·
        refine ⟨13674713392267361732032007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36465902379379631285418685 13674713392267361732032007)
        ·
          refine ⟨20512070088401042598048011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13674713392267361732032007 20512070088401042598048011)
          ·
            refine ⟨30768105132601563897072017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20512070088401042598048011 30768105132601563897072017)
            ·
              refine ⟨23076078849451172922804013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30768105132601563897072017 23076078849451172922804013)
              ·
                refine ⟨8653529568544189846051505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23076078849451172922804013 8653529568544189846051505)
                ·
                  refine ⟨6490147176408142384538629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8653529568544189846051505 6490147176408142384538629)
                  ·
                    refine ⟨1216902595576526697100993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6490147176408142384538629 1216902595576526697100993)
                    ·
                      refine ⟨912676946682395022825745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1216902595576526697100993 912676946682395022825745)
                      ·
                        rfl

theorem cell23_1777432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 2, 4, 2].length) (baseStart_1777432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1777432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1777432 prefixEnd_1777432 := by exact prefixLift 1777432
  have htrace : WordTrace (prefixWord ++ tailWord_1777432) baseStart_1777432 baseEnd_1777432 := by
    simpa [prefixWord, tailWord_1777432, baseEnd_1777432] using wordTrace_append hprefix tailTrace_1777432
  have hstable : (prefixWord ++ tailWord_1777432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777432).length < 2 ^ (prefixWord ++ tailWord_1777432).sum := by decide
  have hdescent : baseEnd_1777432 < baseStart_1777432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777442 : List Nat := [3, 3, 1, 1, 2, 1, 2, 1, 5, 4]
def baseStart_1777442 : Nat := 118140960795 + 1777442 * 2 ^ 59
def prefixEnd_1777442 : Nat := 4983230072969 + 3 ^ 40 * 1777442 * 2
def baseEnd_1777442 : Nat := 304227360496313327900233

theorem tailTrace_1777442 : CollatzResearch.WordTrace tailWord_1777442 prefixEnd_1777442 304227360496313327900233 := by
  unfold tailWord_1777442
  simp only [CollatzResearch.WordTrace]
  refine ⟨16207158906659667942707645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43219090417759114513887053 16207158906659667942707645)
  ·
    refine ⟨6077684589997375478515367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16207158906659667942707645 6077684589997375478515367)
    ·
      refine ⟨9116526884996063217773051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6077684589997375478515367 9116526884996063217773051)
      ·
        refine ⟨13674790327494094826659577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9116526884996063217773051 13674790327494094826659577)
        ·
          refine ⟨10256092745620571119994683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13674790327494094826659577 10256092745620571119994683)
          ·
            refine ⟨15384139118430856679992025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10256092745620571119994683 15384139118430856679992025)
            ·
              refine ⟨11538104338823142509994019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15384139118430856679992025 11538104338823142509994019)
              ·
                refine ⟨17307156508234713764991029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11538104338823142509994019 17307156508234713764991029)
                ·
                  refine ⟨1622545922647004415467909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17307156508234713764991029 1622545922647004415467909)
                  ·
                    refine ⟨304227360496313327900233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1622545922647004415467909 304227360496313327900233)
                    ·
                      rfl

theorem cell23_1777442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_1777442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1777442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1777442 prefixEnd_1777442 := by exact prefixLift 1777442
  have htrace : WordTrace (prefixWord ++ tailWord_1777442) baseStart_1777442 baseEnd_1777442 := by
    simpa [prefixWord, tailWord_1777442, baseEnd_1777442] using wordTrace_append hprefix tailTrace_1777442
  have hstable : (prefixWord ++ tailWord_1777442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777442).length < 2 ^ (prefixWord ++ tailWord_1777442).sum := by decide
  have hdescent : baseEnd_1777442 < baseStart_1777442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777452 : List Nat := [2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 3]
def baseStart_1777452 : Nat := 118140960795 + 1777452 * 2 ^ 59
def prefixEnd_1777452 : Nat := 4983230072969 + 3 ^ 40 * 1777452 * 2
def baseEnd_1777452 : Nat := 912687216295484944575653

theorem tailTrace_1777452 : CollatzResearch.WordTrace tailWord_1777452 prefixEnd_1777452 912687216295484944575653 := by
  unfold tailWord_1777452
  simp only [CollatzResearch.WordTrace]
  refine ⟨32414500178301221739347305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43219333571068295652463073 32414500178301221739347305)
  ·
    refine ⟨24310875133725916304510479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32414500178301221739347305 24310875133725916304510479)
    ·
      refine ⟨36466312700588874456765719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24310875133725916304510479 36466312700588874456765719)
      ·
        refine ⟨54699469050883311685148579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36466312700588874456765719 54699469050883311685148579)
        ·
          refine ⟨82049203576324967527722869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54699469050883311685148579 82049203576324967527722869)
          ·
            refine ⟨7692112835280465705724019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82049203576324967527722869 7692112835280465705724019)
            ·
              refine ⟨11538169252920698558586029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7692112835280465705724019 11538169252920698558586029)
              ·
                refine ⟨4326813469845261959469761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11538169252920698558586029 4326813469845261959469761)
                ·
                  refine ⟨3245110102383946469602321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4326813469845261959469761 3245110102383946469602321)
                  ·
                    refine ⟨2433832576787959852201741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3245110102383946469602321 2433832576787959852201741)
                    ·
                      refine ⟨912687216295484944575653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2433832576787959852201741 912687216295484944575653)
                      ·
                        rfl

theorem cell23_1777452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 3].length) (baseStart_1777452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1777452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1777452 prefixEnd_1777452 := by exact prefixLift 1777452
  have htrace : WordTrace (prefixWord ++ tailWord_1777452) baseStart_1777452 baseEnd_1777452 := by
    simpa [prefixWord, tailWord_1777452, baseEnd_1777452] using wordTrace_append hprefix tailTrace_1777452
  have hstable : (prefixWord ++ tailWord_1777452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777452).length < 2 ^ (prefixWord ++ tailWord_1777452).sum := by decide
  have hdescent : baseEnd_1777452 < baseStart_1777452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777469 : List Nat := [1, 4, 1, 4, 1, 1, 2, 2, 2, 2, 3]
def baseStart_1777469 : Nat := 118140960795 + 1777469 * 2 ^ 59
def prefixEnd_1777469 : Nat := 4983230072969 + 3 ^ 40 * 1777469 * 2
def baseEnd_1777469 : Nat := 912695945466611378063075

theorem tailTrace_1777469 : CollatzResearch.WordTrace tailWord_1777469 prefixEnd_1777469 912695945466611378063075 := by
  unfold tailWord_1777469
  simp only [CollatzResearch.WordTrace]
  refine ⟨64829620397540855382063461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43219746931693903588042307 64829620397540855382063461)
  ·
    refine ⟨12155553824538910384136899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64829620397540855382063461 12155553824538910384136899)
    ·
      refine ⟨18233330736808365576205349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12155553824538910384136899 18233330736808365576205349)
      ·
        refine ⟨3418749513151568545538503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18233330736808365576205349 3418749513151568545538503)
        ·
          refine ⟨5128124269727352818307755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3418749513151568545538503 5128124269727352818307755)
          ·
            refine ⟨7692186404591029227461633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5128124269727352818307755 7692186404591029227461633)
            ·
              refine ⟨5769139803443271920596225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7692186404591029227461633 5769139803443271920596225)
              ·
                refine ⟨4326854852582453940447169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5769139803443271920596225 4326854852582453940447169)
                ·
                  refine ⟨3245141139436840455335377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4326854852582453940447169 3245141139436840455335377)
                  ·
                    refine ⟨2433855854577630341501533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3245141139436840455335377 2433855854577630341501533)
                    ·
                      refine ⟨912695945466611378063075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2433855854577630341501533 912695945466611378063075)
                      ·
                        rfl

theorem cell23_1777469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_1777469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1777469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1777469 prefixEnd_1777469 := by exact prefixLift 1777469
  have htrace : WordTrace (prefixWord ++ tailWord_1777469) baseStart_1777469 baseEnd_1777469 := by
    simpa [prefixWord, tailWord_1777469, baseEnd_1777469] using wordTrace_append hprefix tailTrace_1777469
  have hstable : (prefixWord ++ tailWord_1777469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777469).length < 2 ^ (prefixWord ++ tailWord_1777469).sum := by decide
  have hdescent : baseEnd_1777469 < baseStart_1777469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777516 : List Nat := [2, 2, 1, 1, 4, 2, 1, 5, 1, 1, 3]
def baseStart_1777516 : Nat := 118140960795 + 1777516 * 2 ^ 59
def prefixEnd_1777516 : Nat := 4983230072969 + 3 ^ 40 * 1777516 * 2
def baseEnd_1777516 : Nat := 912720079057372694175359

theorem tailTrace_1777516 : CollatzResearch.WordTrace tailWord_1777516 prefixEnd_1777516 912720079057372694175359 := by
  unfold tailWord_1777516
  simp only [CollatzResearch.WordTrace]
  refine ⟨32415667314185291204512201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43220889752247054939349601 32415667314185291204512201)
  ·
    refine ⟨24311750485638968403384151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32415667314185291204512201 24311750485638968403384151)
    ·
      refine ⟨36467625728458452605076227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24311750485638968403384151 36467625728458452605076227)
      ·
        refine ⟨54701438592687678907614341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36467625728458452605076227 54701438592687678907614341)
        ·
          refine ⟨10256519736128939795177689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54701438592687678907614341 10256519736128939795177689)
          ·
            refine ⟨7692389802096704846383267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10256519736128939795177689 7692389802096704846383267)
            ·
              refine ⟨11538584703145057269574901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7692389802096704846383267 11538584703145057269574901)
              ·
                refine ⟨1081742315919849119022647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11538584703145057269574901 1081742315919849119022647)
                ·
                  refine ⟨1622613473879773678533971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1081742315919849119022647 1622613473879773678533971)
                  ·
                    refine ⟨2433920210819660517800957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1622613473879773678533971 2433920210819660517800957)
                    ·
                      refine ⟨912720079057372694175359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2433920210819660517800957 912720079057372694175359)
                      ·
                        rfl

theorem cell23_1777516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 5, 1, 1, 3].length) (baseStart_1777516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1777516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1777516 prefixEnd_1777516 := by exact prefixLift 1777516
  have htrace : WordTrace (prefixWord ++ tailWord_1777516) baseStart_1777516 baseEnd_1777516 := by
    simpa [prefixWord, tailWord_1777516, baseEnd_1777516] using wordTrace_append hprefix tailTrace_1777516
  have hstable : (prefixWord ++ tailWord_1777516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777516).length < 2 ^ (prefixWord ++ tailWord_1777516).sum := by decide
  have hdescent : baseEnd_1777516 < baseStart_1777516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777535 : List Nat := [1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 6]
def baseStart_1777535 : Nat := 118140960795 + 1777535 * 2 ^ 59
def prefixEnd_1777535 : Nat := 4983230072969 + 3 ^ 40 * 1777535 * 2
def baseEnd_1777535 : Nat := 912729835189808119837771

theorem tailTrace_1777535 : CollatzResearch.WordTrace tailWord_1777535 prefixEnd_1777535 912729835189808119837771 := by
  unfold tailWord_1777535
  simp only [CollatzResearch.WordTrace]
  refine ⟨64832027615301748653966059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43221351743534499102644039 64832027615301748653966059)
  ·
    refine ⟨97248041422952622980949089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64832027615301748653966059 97248041422952622980949089)
    ·
      refine ⟨72936031067214467235711817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97248041422952622980949089 72936031067214467235711817)
      ·
        refine ⟨54702023300410850426783863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72936031067214467235711817 54702023300410850426783863)
        ·
          refine ⟨82053034950616275640175795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54702023300410850426783863 82053034950616275640175795)
          ·
            refine ⟨123079552425924413460263693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82053034950616275640175795 123079552425924413460263693)
            ·
              refine ⟨46154832159721655047598885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123079552425924413460263693 46154832159721655047598885)
              ·
                refine ⟨8654031029947810321424791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46154832159721655047598885 8654031029947810321424791)
                ·
                  refine ⟨12981046544921715482137187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8654031029947810321424791 12981046544921715482137187)
                  ·
                    refine ⟨19471569817382573223205781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12981046544921715482137187 19471569817382573223205781)
                    ·
                      refine ⟨912729835189808119837771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19471569817382573223205781 912729835189808119837771)
                      ·
                        rfl

theorem cell23_1777535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 6].length) (baseStart_1777535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1777535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1777535 prefixEnd_1777535 := by exact prefixLift 1777535
  have htrace : WordTrace (prefixWord ++ tailWord_1777535) baseStart_1777535 baseEnd_1777535 := by
    simpa [prefixWord, tailWord_1777535, baseEnd_1777535] using wordTrace_append hprefix tailTrace_1777535
  have hstable : (prefixWord ++ tailWord_1777535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777535).length < 2 ^ (prefixWord ++ tailWord_1777535).sum := by decide
  have hdescent : baseEnd_1777535 < baseStart_1777535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777545 : List Nat := [1, 2, 1, 1, 5, 1, 2, 10]
def baseStart_1777545 : Nat := 118140960795 + 1777545 * 2 ^ 59
def prefixEnd_1777545 : Nat := 4983230072969 + 3 ^ 40 * 1777545 * 2
def baseEnd_1777545 : Nat := 33804998888753817804175

theorem tailTrace_1777545 : CollatzResearch.WordTrace tailWord_1777545 prefixEnd_1777545 33804998888753817804175 := by
  unfold tailWord_1777545
  simp only [CollatzResearch.WordTrace]
  refine ⟨64832392345265520361830089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43221594896843680241220059 64832392345265520361830089)
  ·
    refine ⟨48624294258949140271372567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64832392345265520361830089 48624294258949140271372567)
    ·
      refine ⟨72936441388423710407058851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48624294258949140271372567 72936441388423710407058851)
      ·
        refine ⟨109404662082635565610588277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72936441388423710407058851 109404662082635565610588277)
        ·
          refine ⟨10256687070247084275992651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 109404662082635565610588277 10256687070247084275992651)
          ·
            refine ⟨15385030605370626413988977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10256687070247084275992651 15385030605370626413988977)
            ·
              refine ⟨11538772954027969810491733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15385030605370626413988977 11538772954027969810491733)
              ·
                refine ⟨33804998888753817804175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 11538772954027969810491733 33804998888753817804175)
                ·
                  rfl

theorem cell23_1777545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 10].length) (baseStart_1777545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1777545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1777545 prefixEnd_1777545 := by exact prefixLift 1777545
  have htrace : WordTrace (prefixWord ++ tailWord_1777545) baseStart_1777545 baseEnd_1777545 := by
    simpa [prefixWord, tailWord_1777545, baseEnd_1777545] using wordTrace_append hprefix tailTrace_1777545
  have hstable : (prefixWord ++ tailWord_1777545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777545).length < 2 ^ (prefixWord ++ tailWord_1777545).sum := by decide
  have hdescent : baseEnd_1777545 < baseStart_1777545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777556 : List Nat := [2, 4, 2, 1, 1, 3, 2, 2, 1, 1, 4]
def baseStart_1777556 : Nat := 118140960795 + 1777556 * 2 ^ 59
def prefixEnd_1777556 : Nat := 4983230072969 + 3 ^ 40 * 1777556 * 2
def baseEnd_1777556 : Nat := 912740618283552537675175

theorem tailTrace_1777556 : CollatzResearch.WordTrace tailWord_1777556 prefixEnd_1777556 912740618283552537675175 := by
  unfold tailWord_1777556
  simp only [CollatzResearch.WordTrace]
  refine ⟨32416396774112834620240261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43221862365483779493653681 32416396774112834620240261)
  ·
    refine ⟨6078074395146156491295049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32416396774112834620240261 6078074395146156491295049)
    ·
      refine ⟨4558555796359617368471287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6078074395146156491295049 4558555796359617368471287)
      ·
        refine ⟨6837833694539426052706931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4558555796359617368471287 6837833694539426052706931)
        ·
          refine ⟨10256750541809139079060397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6837833694539426052706931 10256750541809139079060397)
          ·
            refine ⟨3846281453178427154647649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10256750541809139079060397 3846281453178427154647649)
            ·
              refine ⟨2884711089883820365985737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3846281453178427154647649 2884711089883820365985737)
              ·
                refine ⟨2163533317412865274489303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2884711089883820365985737 2163533317412865274489303)
                ·
                  refine ⟨3245299976119297911733955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2163533317412865274489303 3245299976119297911733955)
                  ·
                    refine ⟨4867949964178946867600933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3245299976119297911733955 4867949964178946867600933)
                    ·
                      refine ⟨912740618283552537675175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4867949964178946867600933 912740618283552537675175)
                      ·
                        rfl

theorem cell23_1777556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_1777556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1777556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1777556 prefixEnd_1777556 := by exact prefixLift 1777556
  have htrace : WordTrace (prefixWord ++ tailWord_1777556) baseStart_1777556 baseEnd_1777556 := by
    simpa [prefixWord, tailWord_1777556, baseEnd_1777556] using wordTrace_append hprefix tailTrace_1777556
  have hstable : (prefixWord ++ tailWord_1777556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777556).length < 2 ^ (prefixWord ++ tailWord_1777556).sum := by decide
  have hdescent : baseEnd_1777556 < baseStart_1777556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777559 : List Nat := [1, 1, 3, 3, 1, 3, 1, 4, 1, 2, 3]
def baseStart_1777559 : Nat := 118140960795 + 1777559 * 2 ^ 59
def prefixEnd_1777559 : Nat := 4983230072969 + 3 ^ 40 * 1777559 * 2
def baseEnd_1777559 : Nat := 912742158725516025937661

theorem tailTrace_1777559 : CollatzResearch.WordTrace tailWord_1777559 prefixEnd_1777559 912742158725516025937661 := by
  unfold tailWord_1777559
  simp only [CollatzResearch.WordTrace]
  refine ⟨64832902967214800752839731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43221935311476533835226487 64832902967214800752839731)
  ·
    refine ⟨97249354450822201129259597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64832902967214800752839731 97249354450822201129259597)
    ·
      refine ⟨36468507919058325423472349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97249354450822201129259597 36468507919058325423472349)
      ·
        refine ⟨13675690469646872033802131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36468507919058325423472349 13675690469646872033802131)
        ·
          refine ⟨20513535704470308050703197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13675690469646872033802131 20513535704470308050703197)
          ·
            refine ⟨7692575889176365519013699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20513535704470308050703197 7692575889176365519013699)
            ·
              refine ⟨11538863833764548278520549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7692575889176365519013699 11538863833764548278520549)
              ·
                refine ⟨2163536968830852802222603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11538863833764548278520549 2163536968830852802222603)
                ·
                  refine ⟨3245305453246279203333905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2163536968830852802222603 3245305453246279203333905)
                  ·
                    refine ⟨2433979089934709402500429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3245305453246279203333905 2433979089934709402500429)
                    ·
                      refine ⟨912742158725516025937661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2433979089934709402500429 912742158725516025937661)
                      ·
                        rfl

theorem cell23_1777559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_1777559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1777559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1777559 prefixEnd_1777559 := by exact prefixLift 1777559
  have htrace : WordTrace (prefixWord ++ tailWord_1777559) baseStart_1777559 baseEnd_1777559 := by
    simpa [prefixWord, tailWord_1777559, baseEnd_1777559] using wordTrace_append hprefix tailTrace_1777559
  have hstable : (prefixWord ++ tailWord_1777559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777559).length < 2 ^ (prefixWord ++ tailWord_1777559).sum := by decide
  have hdescent : baseEnd_1777559 < baseStart_1777559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777562 : List Nat := [3, 1, 1, 4, 2, 2, 1, 9]
def baseStart_1777562 : Nat := 118140960795 + 1777562 * 2 ^ 59
def prefixEnd_1777562 : Nat := 4983230072969 + 3 ^ 40 * 1777562 * 2
def baseEnd_1777562 : Nat := 33805322191388130155561

theorem tailTrace_1777562 : CollatzResearch.WordTrace tailWord_1777562 prefixEnd_1777562 33805322191388130155561 := by
  unfold tailWord_1777562
  simp only [CollatzResearch.WordTrace]
  refine ⟨16208253096550983066299735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43222008257469288176799293 16208253096550983066299735)
  ·
    refine ⟨24312379644826474599449603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16208253096550983066299735 24312379644826474599449603)
    ·
      refine ⟨36468569467239711899174405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24312379644826474599449603 36468569467239711899174405)
      ·
        refine ⟨6837856775107445981095201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36468569467239711899174405 6837856775107445981095201)
        ·
          refine ⟨5128392581330584485821401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6837856775107445981095201 5128392581330584485821401)
          ·
            refine ⟨3846294435997938364366051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5128392581330584485821401 3846294435997938364366051)
            ·
              refine ⟨5769441653996907546549077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3846294435997938364366051 5769441653996907546549077)
              ·
                refine ⟨33805322191388130155561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5769441653996907546549077 33805322191388130155561)
                ·
                  rfl

theorem cell23_1777562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 9].length) (baseStart_1777562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1777562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1777562 prefixEnd_1777562 := by exact prefixLift 1777562
  have htrace : WordTrace (prefixWord ++ tailWord_1777562) baseStart_1777562 baseEnd_1777562 := by
    simpa [prefixWord, tailWord_1777562, baseEnd_1777562] using wordTrace_append hprefix tailTrace_1777562
  have hstable : (prefixWord ++ tailWord_1777562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777562).length < 2 ^ (prefixWord ++ tailWord_1777562).sum := by decide
  have hdescent : baseEnd_1777562 < baseStart_1777562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777599 : List Nat := [1, 1, 2, 2, 2, 1, 4, 2, 3, 3, 2]
def baseStart_1777599 : Nat := 118140960795 + 1777599 * 2 ^ 59
def prefixEnd_1777599 : Nat := 4983230072969 + 3 ^ 40 * 1777599 * 2
def baseEnd_1777599 : Nat := 912762697951695869437477

theorem tailTrace_1777599 : CollatzResearch.WordTrace tailWord_1777599 prefixEnd_1777599 912762697951695869437477 := by
  unfold tailWord_1777599
  simp only [CollatzResearch.WordTrace]
  refine ⟨64834361887069887584295851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43222907924713258389530567 64834361887069887584295851)
  ·
    refine ⟨97251542830604831376443777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64834361887069887584295851 97251542830604831376443777)
    ·
      refine ⟨72938657122953623532332833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97251542830604831376443777 72938657122953623532332833)
      ·
        refine ⟨54703992842215217649249625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72938657122953623532332833 54703992842215217649249625)
        ·
          refine ⟨41027994631661413236937219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54703992842215217649249625 41027994631661413236937219)
          ·
            refine ⟨61541991947492119855405829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41027994631661413236937219 61541991947492119855405829)
            ·
              refine ⟨11539123490154772472888593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61541991947492119855405829 11539123490154772472888593)
              ·
                refine ⟨8654342617616079354666445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11539123490154772472888593 8654342617616079354666445)
                ·
                  refine ⟨3245378481606029757999917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8654342617616079354666445 3245378481606029757999917)
                  ·
                    refine ⟨1217016930602261159249969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3245378481606029757999917 1217016930602261159249969)
                    ·
                      refine ⟨912762697951695869437477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1217016930602261159249969 912762697951695869437477)
                      ·
                        rfl

theorem cell23_1777599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 3, 3, 2].length) (baseStart_1777599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1777599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1777599 prefixEnd_1777599 := by exact prefixLift 1777599
  have htrace : WordTrace (prefixWord ++ tailWord_1777599) baseStart_1777599 baseEnd_1777599 := by
    simpa [prefixWord, tailWord_1777599, baseEnd_1777599] using wordTrace_append hprefix tailTrace_1777599
  have hstable : (prefixWord ++ tailWord_1777599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777599).length < 2 ^ (prefixWord ++ tailWord_1777599).sum := by decide
  have hdescent : baseEnd_1777599 < baseStart_1777599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777616 : List Nat := [2, 1, 1, 1, 1, 2, 7, 2, 1, 3, 2]
def baseStart_1777616 : Nat := 118140960795 + 1777616 * 2 ^ 59
def prefixEnd_1777616 : Nat := 4983230072969 + 3 ^ 40 * 1777616 * 2
def baseEnd_1777616 : Nat := 912771427122822302924899

theorem tailTrace_1777616 : CollatzResearch.WordTrace tailWord_1777616 prefixEnd_1777616 912771427122822302924899 := by
  unfold tailWord_1777616
  simp only [CollatzResearch.WordTrace]
  refine ⟨32417490964004149743832351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43223321285338866325109801 32417490964004149743832351)
  ·
    refine ⟨48626236446006224615748527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32417490964004149743832351 48626236446006224615748527)
    ·
      refine ⟨72939354669009336923622791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48626236446006224615748527 72939354669009336923622791)
      ·
        refine ⟨109409032003514005385434187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72939354669009336923622791 109409032003514005385434187)
        ·
          refine ⟨164113548005271008078151281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109409032003514005385434187 164113548005271008078151281)
          ·
            refine ⟨123085161003953256058613461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164113548005271008078151281 123085161003953256058613461)
            ·
              refine ⟨2884808461030154438873753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 123085161003953256058613461 2884808461030154438873753)
              ·
                refine ⟨2163606345772615829155315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2884808461030154438873753 2163606345772615829155315)
                ·
                  refine ⟨3245409518658923743732973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2163606345772615829155315 3245409518658923743732973)
                  ·
                    refine ⟨1217028569497096403899865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3245409518658923743732973 1217028569497096403899865)
                    ·
                      refine ⟨912771427122822302924899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1217028569497096403899865 912771427122822302924899)
                      ·
                        rfl

theorem cell23_1777616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 2, 1, 3, 2].length) (baseStart_1777616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1777616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1777616 prefixEnd_1777616 := by exact prefixLift 1777616
  have htrace : WordTrace (prefixWord ++ tailWord_1777616) baseStart_1777616 baseEnd_1777616 := by
    simpa [prefixWord, tailWord_1777616, baseEnd_1777616] using wordTrace_append hprefix tailTrace_1777616
  have hstable : (prefixWord ++ tailWord_1777616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777616).length < 2 ^ (prefixWord ++ tailWord_1777616).sum := by decide
  have hdescent : baseEnd_1777616 < baseStart_1777616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777632 : List Nat := [2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 3]
def baseStart_1777632 : Nat := 118140960795 + 1777632 * 2 ^ 59
def prefixEnd_1777632 : Nat := 4983230072969 + 3 ^ 40 * 1777632 * 2
def baseEnd_1777632 : Nat := 912779642813294240324825

theorem tailTrace_1777632 : CollatzResearch.WordTrace tailWord_1777632 prefixEnd_1777632 912779642813294240324825 := by
  unfold tailWord_1777632
  simp only [CollatzResearch.WordTrace]
  refine ⟨32417782747975167110123575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43223710330633556146831433 32417782747975167110123575)
  ·
    refine ⟨48626674121962750665185363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32417782747975167110123575 48626674121962750665185363)
    ·
      refine ⟨72940011182944125997778045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48626674121962750665185363 72940011182944125997778045)
      ·
        refine ⟨27352504193604047249166767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72940011182944125997778045 27352504193604047249166767)
        ·
          refine ⟨41028756290406070873750151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27352504193604047249166767 41028756290406070873750151)
          ·
            refine ⟨61543134435609106310625227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41028756290406070873750151 61543134435609106310625227)
            ·
              refine ⟨92314701653413659465937841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61543134435609106310625227 92314701653413659465937841)
              ·
                refine ⟨69236026240060244599453381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92314701653413659465937841 69236026240060244599453381)
                ·
                  refine ⟨12981754920011295862397509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69236026240060244599453381 12981754920011295862397509)
                  ·
                    refine ⟨2434079047502117974199533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12981754920011295862397509 2434079047502117974199533)
                    ·
                      refine ⟨912779642813294240324825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2434079047502117974199533 912779642813294240324825)
                      ·
                        rfl

theorem cell23_1777632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 3].length) (baseStart_1777632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1777632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1777632 prefixEnd_1777632 := by exact prefixLift 1777632
  have htrace : WordTrace (prefixWord ++ tailWord_1777632) baseStart_1777632 baseEnd_1777632 := by
    simpa [prefixWord, tailWord_1777632, baseEnd_1777632] using wordTrace_append hprefix tailTrace_1777632
  have hstable : (prefixWord ++ tailWord_1777632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777632).length < 2 ^ (prefixWord ++ tailWord_1777632).sum := by decide
  have hdescent : baseEnd_1777632 < baseStart_1777632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777684 : List Nat := [2, 4, 3, 2, 1, 2, 2, 1, 1, 3, 2]
def baseStart_1777684 : Nat := 118140960795 + 1777684 * 2 ^ 59
def prefixEnd_1777684 : Nat := 4983230072969 + 3 ^ 40 * 1777684 * 2
def baseEnd_1777684 : Nat := 912806343807328036874587

theorem tailTrace_1777684 : CollatzResearch.WordTrace tailWord_1777684 prefixEnd_1777684 912806343807328036874587 := by
  unfold tailWord_1777684
  simp only [CollatzResearch.WordTrace]
  refine ⟨32418731045880973550570053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43224974727841298067426737 32418731045880973550570053)
  ·
    refine ⟨6078512071102682540731885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32418731045880973550570053 6078512071102682540731885)
    ·
      refine ⟨2279442026663505952774457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6078512071102682540731885 2279442026663505952774457)
      ·
        refine ⟨1709581519997629464580843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2279442026663505952774457 1709581519997629464580843)
        ·
          refine ⟨2564372279996444196871265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1709581519997629464580843 2564372279996444196871265)
          ·
            refine ⟨1923279209997333147653449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2564372279996444196871265 1923279209997333147653449)
            ·
              refine ⟨1442459407497999860740087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1923279209997333147653449 1442459407497999860740087)
              ·
                refine ⟨2163689111246999791110131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1442459407497999860740087 2163689111246999791110131)
                ·
                  refine ⟨3245533666870499686665197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2163689111246999791110131 3245533666870499686665197)
                  ·
                    refine ⟨1217075125076437382499449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3245533666870499686665197 1217075125076437382499449)
                    ·
                      refine ⟨912806343807328036874587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1217075125076437382499449 912806343807328036874587)
                      ·
                        rfl

theorem cell23_1777684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_1777684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1777684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1777684 prefixEnd_1777684 := by exact prefixLift 1777684
  have htrace : WordTrace (prefixWord ++ tailWord_1777684) baseStart_1777684 baseEnd_1777684 := by
    simpa [prefixWord, tailWord_1777684, baseEnd_1777684] using wordTrace_append hprefix tailTrace_1777684
  have hstable : (prefixWord ++ tailWord_1777684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777684).length < 2 ^ (prefixWord ++ tailWord_1777684).sum := by decide
  have hdescent : baseEnd_1777684 < baseStart_1777684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777697 : List Nat := [1, 2, 3, 2, 5, 1, 1, 2, 2, 2, 2]
def baseStart_1777697 : Nat := 118140960795 + 1777697 * 2 ^ 59
def prefixEnd_1777697 : Nat := 4983230072969 + 3 ^ 40 * 1777697 * 2
def baseEnd_1777697 : Nat := 912813019055836486012027

theorem tailTrace_1777697 : CollatzResearch.WordTrace tailWord_1777697 prefixEnd_1777697 912813019055836486012027 := by
  unfold tailWord_1777697
  simp only [CollatzResearch.WordTrace]
  refine ⟨64837936240714850321363345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43225290827143233547575563 64837936240714850321363345)
  ·
    refine ⟨48628452180536137741022509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64837936240714850321363345 48628452180536137741022509)
    ·
      refine ⟨18235669567701051652883441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48628452180536137741022509 18235669567701051652883441)
      ·
        refine ⟨13676752175775788739662581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18235669567701051652883441 13676752175775788739662581)
        ·
          refine ⟨1282195516478980194343367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13676752175775788739662581 1282195516478980194343367)
          ·
            refine ⟨1923293274718470291515051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1282195516478980194343367 1923293274718470291515051)
            ·
              refine ⟨2884939912077705437272577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1923293274718470291515051 2884939912077705437272577)
              ·
                refine ⟨2163704934058279077954433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2884939912077705437272577 2163704934058279077954433)
                ·
                  refine ⟨1622778700543709308465825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2163704934058279077954433 1622778700543709308465825)
                  ·
                    refine ⟨1217084025407781981349369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1622778700543709308465825 1217084025407781981349369)
                    ·
                      refine ⟨912813019055836486012027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1217084025407781981349369 912813019055836486012027)
                      ·
                        rfl

theorem cell23_1777697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 2, 2, 2, 2].length) (baseStart_1777697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1777697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1777697 prefixEnd_1777697 := by exact prefixLift 1777697
  have htrace : WordTrace (prefixWord ++ tailWord_1777697) baseStart_1777697 baseEnd_1777697 := by
    simpa [prefixWord, tailWord_1777697, baseEnd_1777697] using wordTrace_append hprefix tailTrace_1777697
  have hstable : (prefixWord ++ tailWord_1777697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777697).length < 2 ^ (prefixWord ++ tailWord_1777697).sum := by decide
  have hdescent : baseEnd_1777697 < baseStart_1777697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777756 : List Nat := [2, 2, 4, 1, 1, 2, 1, 1, 4, 2, 3]
def baseStart_1777756 : Nat := 118140960795 + 1777756 * 2 ^ 59
def prefixEnd_1777756 : Nat := 4983230072969 + 3 ^ 40 * 1777756 * 2
def baseEnd_1777756 : Nat := 912843314414451755174255

theorem tailTrace_1777756 : CollatzResearch.WordTrace tailWord_1777756 prefixEnd_1777756 912843314414451755174255 := by
  unfold tailWord_1777756
  simp only [CollatzResearch.WordTrace]
  refine ⟨32420044073750551698880561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43226725431667402265174081 32420044073750551698880561)
  ·
    refine ⟨24315033055312913774160421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32420044073750551698880561 24315033055312913774160421)
    ·
      refine ⟨4559068697871171332655079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24315033055312913774160421 4559068697871171332655079)
      ·
        refine ⟨6838603046806756998982619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4559068697871171332655079 6838603046806756998982619)
        ·
          refine ⟨10257904570210135498473929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6838603046806756998982619 10257904570210135498473929)
          ·
            refine ⟨7693428427657601623855447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10257904570210135498473929 7693428427657601623855447)
            ·
              refine ⟨11540142641486402435783171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7693428427657601623855447 11540142641486402435783171)
              ·
                refine ⟨17310213962229603653674757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11540142641486402435783171 17310213962229603653674757)
                ·
                  refine ⟨3245665117918050685064017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17310213962229603653674757 3245665117918050685064017)
                  ·
                    refine ⟨2434248838438538013798013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3245665117918050685064017 2434248838438538013798013)
                    ·
                      refine ⟨912843314414451755174255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2434248838438538013798013 912843314414451755174255)
                      ·
                        rfl

theorem cell23_1777756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_1777756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1777756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1777756 prefixEnd_1777756 := by exact prefixLift 1777756
  have htrace : WordTrace (prefixWord ++ tailWord_1777756) baseStart_1777756 baseEnd_1777756 := by
    simpa [prefixWord, tailWord_1777756, baseEnd_1777756] using wordTrace_append hprefix tailTrace_1777756
  have hstable : (prefixWord ++ tailWord_1777756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777756).length < 2 ^ (prefixWord ++ tailWord_1777756).sum := by decide
  have hdescent : baseEnd_1777756 < baseStart_1777756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777776 : List Nat := [2, 1, 1, 1, 5, 2, 4, 1, 6]
def baseStart_1777776 : Nat := 118140960795 + 1777776 * 2 ^ 59
def prefixEnd_1777776 : Nat := 4983230072969 + 3 ^ 40 * 1777776 * 2
def baseEnd_1777776 : Nat := 101428176003060186324907

theorem tailTrace_1777776 : CollatzResearch.WordTrace tailWord_1777776 prefixEnd_1777776 101428176003060186324907 := by
  unfold tailWord_1777776
  simp only [CollatzResearch.WordTrace]
  refine ⟨32420408803714323406744591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43227211738285764542326121 32420408803714323406744591)
  ·
    refine ⟨48630613205571485110116887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32420408803714323406744591 48630613205571485110116887)
    ·
      refine ⟨72945919808357227665175331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48630613205571485110116887 72945919808357227665175331)
      ·
        refine ⟨109418879712535841497762997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72945919808357227665175331 109418879712535841497762997)
        ·
          refine ⟨10258019973050235140415281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 109418879712535841497762997 10258019973050235140415281)
          ·
            refine ⟨7693514979787676355311461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10258019973050235140415281 7693514979787676355311461)
            ·
              refine ⟨1442534058710189316620899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7693514979787676355311461 1442534058710189316620899)
              ·
                refine ⟨2163801088065283974931349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1442534058710189316620899 2163801088065283974931349)
                ·
                  refine ⟨101428176003060186324907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2163801088065283974931349 101428176003060186324907)
                  ·
                    rfl

theorem cell23_1777776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 1, 6].length) (baseStart_1777776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1777776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1777776 prefixEnd_1777776 := by exact prefixLift 1777776
  have htrace : WordTrace (prefixWord ++ tailWord_1777776) baseStart_1777776 baseEnd_1777776 := by
    simpa [prefixWord, tailWord_1777776, baseEnd_1777776] using wordTrace_append hprefix tailTrace_1777776
  have hstable : (prefixWord ++ tailWord_1777776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777776).length < 2 ^ (prefixWord ++ tailWord_1777776).sum := by decide
  have hdescent : baseEnd_1777776 < baseStart_1777776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777820 : List Nat := [2, 2, 3, 2, 1, 1, 3, 4, 1, 1, 3]
def baseStart_1777820 : Nat := 118140960795 + 1777820 * 2 ^ 59
def prefixEnd_1777820 : Nat := 4983230072969 + 3 ^ 40 * 1777820 * 2
def baseEnd_1777820 : Nat := 912876177176339504773961

theorem tailTrace_1777820 : CollatzResearch.WordTrace tailWord_1777820 prefixEnd_1777820 912876177176339504773961 := by
  unfold tailWord_1777820
  simp only [CollatzResearch.WordTrace]
  refine ⟨32421211209634621164045457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43228281612846161552060609 32421211209634621164045457)
  ·
    refine ⟨24315908407225965873034093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32421211209634621164045457 24315908407225965873034093)
    ·
      refine ⟨9118465652709737202387785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24315908407225965873034093 9118465652709737202387785)
      ·
        refine ⟨6838849239532302901790839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9118465652709737202387785 6838849239532302901790839)
        ·
          refine ⟨10258273859298454352686259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6838849239532302901790839 10258273859298454352686259)
          ·
            refine ⟨15387410788947681529029389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10258273859298454352686259 15387410788947681529029389)
            ·
              refine ⟨5770279045855380573386021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15387410788947681529029389 5770279045855380573386021)
              ·
                refine ⟨1081927321097883857509879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5770279045855380573386021 1081927321097883857509879)
                ·
                  refine ⟨1622890981646825786264819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1081927321097883857509879 1622890981646825786264819)
                  ·
                    refine ⟨2434336472470238679397229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1622890981646825786264819 2434336472470238679397229)
                    ·
                      refine ⟨912876177176339504773961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2434336472470238679397229 912876177176339504773961)
                      ·
                        rfl

theorem cell23_1777820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_1777820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1777820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1777820 prefixEnd_1777820 := by exact prefixLift 1777820
  have htrace : WordTrace (prefixWord ++ tailWord_1777820) baseStart_1777820 baseEnd_1777820 := by
    simpa [prefixWord, tailWord_1777820, baseEnd_1777820] using wordTrace_append hprefix tailTrace_1777820
  have hstable : (prefixWord ++ tailWord_1777820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777820).length < 2 ^ (prefixWord ++ tailWord_1777820).sum := by decide
  have hdescent : baseEnd_1777820 < baseStart_1777820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777829 : List Nat := [1, 3, 1, 2, 1, 3, 2, 1, 3, 1, 5]
def baseStart_1777829 : Nat := 118140960795 + 1777829 * 2 ^ 59
def prefixEnd_1777829 : Nat := 4983230072969 + 3 ^ 40 * 1777829 * 2
def baseEnd_1777829 : Nat := 912880798502229969561419

theorem tailTrace_1777829 : CollatzResearch.WordTrace tailWord_1777829 prefixEnd_1777829 912880798502229969561419 := by
  unfold tailWord_1777829
  simp only [CollatzResearch.WordTrace]
  refine ⟨64842750676236636865168541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43228500450824424576779027 64842750676236636865168541)
  ·
    refine ⟨24316031503588738824438203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64842750676236636865168541 24316031503588738824438203)
    ·
      refine ⟨36474047255383108236657305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24316031503588738824438203 36474047255383108236657305)
      ·
        refine ⟨27355535441537331177492979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36474047255383108236657305 27355535441537331177492979)
        ·
          refine ⟨41033303162305996766239469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27355535441537331177492979 41033303162305996766239469)
          ·
            refine ⟨15387488685864748787339801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41033303162305996766239469 15387488685864748787339801)
            ·
              refine ⟨11540616514398561590504851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15387488685864748787339801 11540616514398561590504851)
              ·
                refine ⟨17310924771597842385757277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11540616514398561590504851 17310924771597842385757277)
                ·
                  refine ⟨6491596789349190894658979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17310924771597842385757277 6491596789349190894658979)
                  ·
                    refine ⟨9737395184023786341988469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6491596789349190894658979 9737395184023786341988469)
                    ·
                      refine ⟨912880798502229969561419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9737395184023786341988469 912880798502229969561419)
                      ·
                        rfl

theorem cell23_1777829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_1777829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1777829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1777829 prefixEnd_1777829 := by exact prefixLift 1777829
  have htrace : WordTrace (prefixWord ++ tailWord_1777829) baseStart_1777829 baseEnd_1777829 := by
    simpa [prefixWord, tailWord_1777829, baseEnd_1777829] using wordTrace_append hprefix tailTrace_1777829
  have hstable : (prefixWord ++ tailWord_1777829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777829).length < 2 ^ (prefixWord ++ tailWord_1777829).sum := by decide
  have hdescent : baseEnd_1777829 < baseStart_1777829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777856 : List Nat := [2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 4]
def baseStart_1777856 : Nat := 118140960795 + 1777856 * 2 ^ 59
def prefixEnd_1777856 : Nat := 4983230072969 + 3 ^ 40 * 1777856 * 2
def baseEnd_1777856 : Nat := 912894662479901363923795

theorem tailTrace_1777856 : CollatzResearch.WordTrace tailWord_1777856 prefixEnd_1777856 912894662479901363923795 := by
  unfold tailWord_1777856
  simp only [CollatzResearch.WordTrace]
  refine ⟨32421867723569410238200711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43229156964759213650934281 32421867723569410238200711)
  ·
    refine ⟨48632801585354115357301067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32421867723569410238200711 48632801585354115357301067)
    ·
      refine ⟨72949202378031173035951601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48632801585354115357301067 72949202378031173035951601)
      ·
        refine ⟨54711901783523379776963701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72949202378031173035951601 54711901783523379776963701)
        ·
          refine ⟨5129240792205316854090347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54711901783523379776963701 5129240792205316854090347)
          ·
            refine ⟨7693861188307975281135521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5129240792205316854090347 7693861188307975281135521)
            ·
              refine ⟨5770395891230981460851641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7693861188307975281135521 5770395891230981460851641)
              ·
                refine ⟨4327796918423236095638731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5770395891230981460851641 4327796918423236095638731)
                ·
                  refine ⟨6491695377634854143458097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4327796918423236095638731 6491695377634854143458097)
                  ·
                    refine ⟨4868771533226140607593573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6491695377634854143458097 4868771533226140607593573)
                    ·
                      refine ⟨912894662479901363923795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4868771533226140607593573 912894662479901363923795)
                      ·
                        rfl

theorem cell23_1777856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 4].length) (baseStart_1777856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1777856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1777856 prefixEnd_1777856 := by exact prefixLift 1777856
  have htrace : WordTrace (prefixWord ++ tailWord_1777856) baseStart_1777856 baseEnd_1777856 := by
    simpa [prefixWord, tailWord_1777856, baseEnd_1777856] using wordTrace_append hprefix tailTrace_1777856
  have hstable : (prefixWord ++ tailWord_1777856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777856).length < 2 ^ (prefixWord ++ tailWord_1777856).sum := by decide
  have hdescent : baseEnd_1777856 < baseStart_1777856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777857 : List Nat := [1, 2, 6, 1, 2, 2, 2, 1, 1, 5]
def baseStart_1777857 : Nat := 118140960795 + 1777857 * 2 ^ 59
def prefixEnd_1777857 : Nat := 4983230072969 + 3 ^ 40 * 1777857 * 2
def baseEnd_1777857 : Nat := 304298391986851953337097

theorem tailTrace_1777857 : CollatzResearch.WordTrace tailWord_1777857 prefixEnd_1777857 304298391986851953337097 := by
  unfold tailWord_1777857
  simp only [CollatzResearch.WordTrace]
  refine ⟨64843771920135197647187825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43229181280090131764791883 64843771920135197647187825)
  ·
    refine ⟨48632828940101398235390869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64843771920135197647187825 48632828940101398235390869)
    ·
      refine ⟨2279663856567253042283947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 48632828940101398235390869 2279663856567253042283947)
      ·
        refine ⟨3419495784850879563425921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2279663856567253042283947 3419495784850879563425921)
        ·
          refine ⟨2564621838638159672569441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3419495784850879563425921 2564621838638159672569441)
          ·
            refine ⟨1923466378978619754427081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2564621838638159672569441 1923466378978619754427081)
            ·
              refine ⟨1442599784233964815820311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1923466378978619754427081 1442599784233964815820311)
              ·
                refine ⟨2163899676350947223730467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1442599784233964815820311 2163899676350947223730467)
                ·
                  refine ⟨3245849514526420835595701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2163899676350947223730467 3245849514526420835595701)
                  ·
                    refine ⟨304298391986851953337097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3245849514526420835595701 304298391986851953337097)
                    ·
                      rfl

theorem cell23_1777857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_1777857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1777857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1777857 prefixEnd_1777857 := by exact prefixLift 1777857
  have htrace : WordTrace (prefixWord ++ tailWord_1777857) baseStart_1777857 baseEnd_1777857 := by
    simpa [prefixWord, tailWord_1777857, baseEnd_1777857] using wordTrace_append hprefix tailTrace_1777857
  have hstable : (prefixWord ++ tailWord_1777857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777857).length < 2 ^ (prefixWord ++ tailWord_1777857).sum := by decide
  have hdescent : baseEnd_1777857 < baseStart_1777857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777859 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 2, 7, 3]
def baseStart_1777859 : Nat := 118140960795 + 1777859 * 2 ^ 59
def prefixEnd_1777859 : Nat := 4983230072969 + 3 ^ 40 * 1777859 * 2
def baseEnd_1777859 : Nat := 912896202921864852186281

theorem tailTrace_1777859 : CollatzResearch.WordTrace tailWord_1777859 prefixEnd_1777859 912896202921864852186281 := by
  unfold tailWord_1777859
  simp only [CollatzResearch.WordTrace]
  refine ⟨64843844866127951988760631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43229229910751967992507087 64843844866127951988760631)
  ·
    refine ⟨97265767299191927983140947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64843844866127951988760631 97265767299191927983140947)
    ·
      refine ⟨145898650948787891974711421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97265767299191927983140947 145898650948787891974711421)
      ·
        refine ⟨54711994105795459490516783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145898650948787891974711421 54711994105795459490516783)
        ·
          refine ⟨82067991158693189235775175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54711994105795459490516783 82067991158693189235775175)
          ·
            refine ⟨123101986738039783853662763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82067991158693189235775175 123101986738039783853662763)
            ·
              refine ⟨184652980107059675780494145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123101986738039783853662763 184652980107059675780494145)
              ·
                refine ⟨138489735080294756835370609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184652980107059675780494145 138489735080294756835370609)
                ·
                  refine ⟨103867301310221067626527957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138489735080294756835370609 103867301310221067626527957)
                  ·
                    refine ⟨2434389874458306272496749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 103867301310221067626527957 2434389874458306272496749)
                    ·
                      refine ⟨912896202921864852186281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2434389874458306272496749 912896202921864852186281)
                      ·
                        rfl

theorem cell23_1777859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 7, 3].length) (baseStart_1777859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1777859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1777859 prefixEnd_1777859 := by exact prefixLift 1777859
  have htrace : WordTrace (prefixWord ++ tailWord_1777859) baseStart_1777859 baseEnd_1777859 := by
    simpa [prefixWord, tailWord_1777859, baseEnd_1777859] using wordTrace_append hprefix tailTrace_1777859
  have hstable : (prefixWord ++ tailWord_1777859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777859).length < 2 ^ (prefixWord ++ tailWord_1777859).sum := by decide
  have hdescent : baseEnd_1777859 < baseStart_1777859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777860 : List Nat := [2, 3, 3, 1, 2, 1, 4, 1, 1, 1, 4]
def baseStart_1777860 : Nat := 118140960795 + 1777860 * 2 ^ 59
def prefixEnd_1777860 : Nat := 4983230072969 + 3 ^ 40 * 1777860 * 2
def baseEnd_1777860 : Nat := 912896716402519348273777

theorem tailTrace_1777860 : CollatzResearch.WordTrace tailWord_1777860 prefixEnd_1777860 912896716402519348273777 := by
  unfold tailWord_1777860
  simp only [CollatzResearch.WordTrace]
  refine ⟨32421940669562164579773517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43229254226082886106364689 32421940669562164579773517)
  ·
    refine ⟨12158227751085811717415069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32421940669562164579773517 12158227751085811717415069)
    ·
      refine ⟨4559335406657179394030651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12158227751085811717415069 4559335406657179394030651)
      ·
        refine ⟨6839003109985769091045977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4559335406657179394030651 6839003109985769091045977)
        ·
          refine ⟨5129252332489326818284483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6839003109985769091045977 5129252332489326818284483)
          ·
            refine ⟨7693878498733990227426725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5129252332489326818284483 7693878498733990227426725)
            ·
              refine ⟨1442602218512623167642511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7693878498733990227426725 1442602218512623167642511)
              ·
                refine ⟨2163903327768934751463767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1442602218512623167642511 2163903327768934751463767)
                ·
                  refine ⟨3245854991653402127195651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2163903327768934751463767 3245854991653402127195651)
                  ·
                    refine ⟨4868782487480103190793477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3245854991653402127195651 4868782487480103190793477)
                    ·
                      refine ⟨912896716402519348273777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4868782487480103190793477 912896716402519348273777)
                      ·
                        rfl

theorem cell23_1777860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_1777860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1777860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1777860 prefixEnd_1777860 := by exact prefixLift 1777860
  have htrace : WordTrace (prefixWord ++ tailWord_1777860) baseStart_1777860 baseEnd_1777860 := by
    simpa [prefixWord, tailWord_1777860, baseEnd_1777860] using wordTrace_append hprefix tailTrace_1777860
  have hstable : (prefixWord ++ tailWord_1777860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777860).length < 2 ^ (prefixWord ++ tailWord_1777860).sum := by decide
  have hdescent : baseEnd_1777860 < baseStart_1777860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777870 : List Nat := [4, 1, 1, 1, 4, 3, 1, 2, 2, 4]
def baseStart_1777870 : Nat := 118140960795 + 1777870 * 2 ^ 59
def prefixEnd_1777870 : Nat := 4983230072969 + 3 ^ 40 * 1777870 * 2
def baseEnd_1777870 : Nat := 304300617069688103049577

theorem tailTrace_1777870 : CollatzResearch.WordTrace tailWord_1777870 prefixEnd_1777870 304300617069688103049577 := by
  unfold tailWord_1777870
  simp only [CollatzResearch.WordTrace]
  refine ⟨8105530758636012608426383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43229497379392067244940709 8105530758636012608426383)
  ·
    refine ⟨12158296137954018912639575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8105530758636012608426383 12158296137954018912639575)
    ·
      refine ⟨18237444206931028368959363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12158296137954018912639575 18237444206931028368959363)
      ·
        refine ⟨27356166310396542553439045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18237444206931028368959363 27356166310396542553439045)
        ·
          refine ⟨5129281183199351728769821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27356166310396542553439045 5129281183199351728769821)
          ·
            refine ⟨1923480443699756898288683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5129281183199351728769821 1923480443699756898288683)
            ·
              refine ⟨2885220665549635347433025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1923480443699756898288683 2885220665549635347433025)
              ·
                refine ⟨2163915499162226510574769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2885220665549635347433025 2163915499162226510574769)
                ·
                  refine ⟨1622936624371669882931077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2163915499162226510574769 1622936624371669882931077)
                  ·
                    refine ⟨304300617069688103049577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1622936624371669882931077 304300617069688103049577)
                    ·
                      rfl

theorem cell23_1777870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 2, 2, 4].length) (baseStart_1777870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1777870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1777870 prefixEnd_1777870 := by exact prefixLift 1777870
  have htrace : WordTrace (prefixWord ++ tailWord_1777870) baseStart_1777870 baseEnd_1777870 := by
    simpa [prefixWord, tailWord_1777870, baseEnd_1777870] using wordTrace_append hprefix tailTrace_1777870
  have hstable : (prefixWord ++ tailWord_1777870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777870).length < 2 ^ (prefixWord ++ tailWord_1777870).sum := by decide
  have hdescent : baseEnd_1777870 < baseStart_1777870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777877 : List Nat := [1, 3, 2, 4, 2, 1, 2, 1, 3, 2, 2]
def baseStart_1777877 : Nat := 118140960795 + 1777877 * 2 ^ 59
def prefixEnd_1777877 : Nat := 4983230072969 + 3 ^ 40 * 1777877 * 2
def baseEnd_1777877 : Nat := 912905445573645781761199

theorem tailTrace_1777877 : CollatzResearch.WordTrace tailWord_1777877 prefixEnd_1777877 912905445573645781761199 := by
  unfold tailWord_1777877
  simp only [CollatzResearch.WordTrace]
  refine ⟨64844501380062741062915885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43229667586708494041943923 64844501380062741062915885)
  ·
    refine ⟨24316688017523527898593457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64844501380062741062915885 24316688017523527898593457)
    ·
      refine ⟨18237516013142645923945093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24316688017523527898593457 18237516013142645923945093)
      ·
        refine ⟨3419534252464246110739705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18237516013142645923945093 3419534252464246110739705)
        ·
          refine ⟨2564650689348184583054779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3419534252464246110739705 2564650689348184583054779)
          ·
            refine ⟨3846976034022276874582169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2564650689348184583054779 3846976034022276874582169)
            ·
              refine ⟨2885232025516707655936627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3846976034022276874582169 2885232025516707655936627)
              ·
                refine ⟨4327848038275061483904941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2885232025516707655936627 4327848038275061483904941)
                ·
                  refine ⟨1622943014353148056464353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4327848038275061483904941 1622943014353148056464353)
                  ·
                    refine ⟨1217207260764861042348265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1622943014353148056464353 1217207260764861042348265)
                    ·
                      refine ⟨912905445573645781761199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1217207260764861042348265 912905445573645781761199)
                      ·
                        rfl

theorem cell23_1777877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_1777877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1777877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1777877 prefixEnd_1777877 := by exact prefixLift 1777877
  have htrace : WordTrace (prefixWord ++ tailWord_1777877) baseStart_1777877 baseEnd_1777877 := by
    simpa [prefixWord, tailWord_1777877, baseEnd_1777877] using wordTrace_append hprefix tailTrace_1777877
  have hstable : (prefixWord ++ tailWord_1777877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777877).length < 2 ^ (prefixWord ++ tailWord_1777877).sum := by decide
  have hdescent : baseEnd_1777877 < baseStart_1777877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777893 : List Nat := [1, 3, 1, 4, 2, 1, 3, 1, 1, 3, 3]
def baseStart_1777893 : Nat := 118140960795 + 1777893 * 2 ^ 59
def prefixEnd_1777893 : Nat := 4983230072969 + 3 ^ 40 * 1777893 * 2
def baseEnd_1777893 : Nat := 912913661264117719161125

theorem tailTrace_1777893 : CollatzResearch.WordTrace tailWord_1777893 prefixEnd_1777893 912913661264117719161125 := by
  unfold tailWord_1777893
  simp only [CollatzResearch.WordTrace]
  refine ⟨64845084948004775795498333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43230056632003183863665555 64845084948004775795498333)
  ·
    refine ⟨24316906855501790923311875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64845084948004775795498333 24316906855501790923311875)
    ·
      refine ⟨36475360283252686384967813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24316906855501790923311875 36475360283252686384967813)
      ·
        refine ⟨6839130053109878697181465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36475360283252686384967813 6839130053109878697181465)
        ·
          refine ⟨5129347539832409022886099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6839130053109878697181465 5129347539832409022886099)
          ·
            refine ⟨7694021309748613534329149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5129347539832409022886099 7694021309748613534329149)
            ·
              refine ⟨2885257991155730075373431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7694021309748613534329149 2885257991155730075373431)
              ·
                refine ⟨4327886986733595113060147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2885257991155730075373431 4327886986733595113060147)
                ·
                  refine ⟨6491830480100392669590221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4327886986733595113060147 6491830480100392669590221)
                  ·
                    refine ⟨2434436430037647251096333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6491830480100392669590221 2434436430037647251096333)
                    ·
                      refine ⟨912913661264117719161125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2434436430037647251096333 912913661264117719161125)
                      ·
                        rfl

theorem cell23_1777893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_1777893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1777893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1777893 prefixEnd_1777893 := by exact prefixLift 1777893
  have htrace : WordTrace (prefixWord ++ tailWord_1777893) baseStart_1777893 baseEnd_1777893 := by
    simpa [prefixWord, tailWord_1777893, baseEnd_1777893] using wordTrace_append hprefix tailTrace_1777893
  have hstable : (prefixWord ++ tailWord_1777893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777893).length < 2 ^ (prefixWord ++ tailWord_1777893).sum := by decide
  have hdescent : baseEnd_1777893 < baseStart_1777893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777906 : List Nat := [3, 2, 1, 3, 2, 1, 1, 1, 2, 2, 5]
def baseStart_1777906 : Nat := 118140960795 + 1777906 * 2 ^ 59
def prefixEnd_1777906 : Nat := 4983230072969 + 3 ^ 40 * 1777906 * 2
def baseEnd_1777906 : Nat := 912920336512626168298565

theorem tailTrace_1777906 : CollatzResearch.WordTrace tailWord_1777906 prefixEnd_1777906 912920336512626168298565 := by
  unfold tailWord_1777906
  simp only [CollatzResearch.WordTrace]
  refine ⟨16211389774239419753930393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43230372731305119343814381 16211389774239419753930393)
  ·
    refine ⟨12158542330679564815447795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16211389774239419753930393 12158542330679564815447795)
    ·
      refine ⟨18237813496019347223171693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12158542330679564815447795 18237813496019347223171693)
      ·
        refine ⟨6839180061007255208689385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18237813496019347223171693 6839180061007255208689385)
        ·
          refine ⟨5129385045755441406517039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6839180061007255208689385 5129385045755441406517039)
          ·
            refine ⟨7694077568633162109775559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5129385045755441406517039 7694077568633162109775559)
            ·
              refine ⟨11541116352949743164663339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7694077568633162109775559 11541116352949743164663339)
              ·
                refine ⟨17311674529424614746995009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11541116352949743164663339 17311674529424614746995009)
                ·
                  refine ⟨12983755897068461060246257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17311674529424614746995009 12983755897068461060246257)
                  ·
                    refine ⟨9737816922801345795184693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12983755897068461060246257 9737816922801345795184693)
                    ·
                      refine ⟨912920336512626168298565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9737816922801345795184693 912920336512626168298565)
                      ·
                        rfl

theorem cell23_1777906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_1777906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1777906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1777906 prefixEnd_1777906 := by exact prefixLift 1777906
  have htrace : WordTrace (prefixWord ++ tailWord_1777906) baseStart_1777906 baseEnd_1777906 := by
    simpa [prefixWord, tailWord_1777906, baseEnd_1777906] using wordTrace_append hprefix tailTrace_1777906
  have hstable : (prefixWord ++ tailWord_1777906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777906).length < 2 ^ (prefixWord ++ tailWord_1777906).sum := by decide
  have hdescent : baseEnd_1777906 < baseStart_1777906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777973 : List Nat := [1, 3, 3, 1, 2, 1, 2, 5, 5]
def baseStart_1777973 : Nat := 118140960795 + 1777973 * 2 ^ 59
def prefixEnd_1777973 : Nat := 4983230072969 + 3 ^ 40 * 1777973 * 2
def baseEnd_1777973 : Nat := 101439415524053045128973

theorem tailTrace_1777973 : CollatzResearch.WordTrace tailWord_1777973 prefixEnd_1777973 101439415524053045128973 := by
  unfold tailWord_1777973
  simp only [CollatzResearch.WordTrace]
  refine ⟨64848002787714949458410573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43232001858476632972273715 64848002787714949458410573)
  ·
    refine ⟨24318001045393106046903965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64848002787714949458410573 24318001045393106046903965)
    ·
      refine ⟨9119250392022414767588987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24318001045393106046903965 9119250392022414767588987)
      ·
        refine ⟨13678875588033622151383481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9119250392022414767588987 13678875588033622151383481)
        ·
          refine ⟨10259156691025216613537611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13678875588033622151383481 10259156691025216613537611)
          ·
            refine ⟨15388735036537824920306417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10259156691025216613537611 15388735036537824920306417)
            ·
              refine ⟨11541551277403368690229813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15388735036537824920306417 11541551277403368690229813)
              ·
                refine ⟨1082020432256565814709045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11541551277403368690229813 1082020432256565814709045)
                ·
                  refine ⟨101439415524053045128973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1082020432256565814709045 101439415524053045128973)
                  ·
                    rfl

theorem cell23_1777973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 5, 5].length) (baseStart_1777973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1777973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1777973 prefixEnd_1777973 := by exact prefixLift 1777973
  have htrace : WordTrace (prefixWord ++ tailWord_1777973) baseStart_1777973 baseEnd_1777973 := by
    simpa [prefixWord, tailWord_1777973, baseEnd_1777973] using wordTrace_append hprefix tailTrace_1777973
  have hstable : (prefixWord ++ tailWord_1777973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777973).length < 2 ^ (prefixWord ++ tailWord_1777973).sum := by decide
  have hdescent : baseEnd_1777973 < baseStart_1777973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777979 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 7]
def baseStart_1777979 : Nat := 118140960795 + 1777979 * 2 ^ 59
def prefixEnd_1777979 : Nat := 4983230072969 + 3 ^ 40 * 1777979 * 2
def baseEnd_1777979 : Nat := 912957820600404382685729

theorem tailTrace_1777979 : CollatzResearch.WordTrace tailWord_1777979 prefixEnd_1777979 912957820600404382685729 := by
  unfold tailWord_1777979
  simp only [CollatzResearch.WordTrace]
  refine ⟨64848221625693212483128991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43232147750462141655419327 64848221625693212483128991)
  ·
    refine ⟨97272332438539818724693487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64848221625693212483128991 97272332438539818724693487)
    ·
      refine ⟨145908498657809728087040231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97272332438539818724693487 145908498657809728087040231)
      ·
        refine ⟨218862747986714592130560347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145908498657809728087040231 218862747986714592130560347)
        ·
          refine ⟨328294121980071888195840521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218862747986714592130560347 328294121980071888195840521)
          ·
            refine ⟨246220591485053916146880391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 328294121980071888195840521 246220591485053916146880391)
            ·
              refine ⟨369330887227580874220320587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246220591485053916146880391 369330887227580874220320587)
              ·
                refine ⟨553996330841371311330480881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 369330887227580874220320587 553996330841371311330480881)
                ·
                  refine ⟨415497248131028483497860661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 553996330841371311330480881 415497248131028483497860661)
                  ·
                    refine ⟨38952867012283920327924437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 415497248131028483497860661 38952867012283920327924437)
                    ·
                      refine ⟨912957820600404382685729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 38952867012283920327924437 912957820600404382685729)
                      ·
                        rfl

theorem cell23_1777979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 7].length) (baseStart_1777979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1777979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1777979 prefixEnd_1777979 := by exact prefixLift 1777979
  have htrace : WordTrace (prefixWord ++ tailWord_1777979) baseStart_1777979 baseEnd_1777979 := by
    simpa [prefixWord, tailWord_1777979, baseEnd_1777979] using wordTrace_append hprefix tailTrace_1777979
  have hstable : (prefixWord ++ tailWord_1777979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777979).length < 2 ^ (prefixWord ++ tailWord_1777979).sum := by decide
  have hdescent : baseEnd_1777979 < baseStart_1777979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1777996 : List Nat := [2, 2, 1, 3, 2, 1, 1, 3, 1, 2, 5]
def baseStart_1777996 : Nat := 118140960795 + 1777996 * 2 ^ 59
def prefixEnd_1777996 : Nat := 4983230072969 + 3 ^ 40 * 1777996 * 2
def baseEnd_1777996 : Nat := 912966549771530816173151

theorem tailTrace_1777996 : CollatzResearch.WordTrace tailWord_1777996 prefixEnd_1777996 912966549771530816173151 := by
  unfold tailWord_1777996
  simp only [CollatzResearch.WordTrace]
  refine ⟨32424420833315812193248921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43232561111087749590998561 32424420833315812193248921)
  ·
    refine ⟨24318315624986859144936691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32424420833315812193248921 24318315624986859144936691)
    ·
      refine ⟨36477473437480288717405037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24318315624986859144936691 36477473437480288717405037)
      ·
        refine ⟨13679052539055108269026889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36477473437480288717405037 13679052539055108269026889)
        ·
          refine ⟨10259289404291331201770167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13679052539055108269026889 10259289404291331201770167)
          ·
            refine ⟨15388934106436996802655251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10259289404291331201770167 15388934106436996802655251)
            ·
              refine ⟨23083401159655495203982877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15388934106436996802655251 23083401159655495203982877)
              ·
                refine ⟨8656275434870810701493579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23083401159655495203982877 8656275434870810701493579)
                ·
                  refine ⟨12984413152306216052240369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8656275434870810701493579 12984413152306216052240369)
                  ·
                    refine ⟨9738309864229662039180277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12984413152306216052240369 9738309864229662039180277)
                    ·
                      refine ⟨912966549771530816173151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9738309864229662039180277 912966549771530816173151)
                      ·
                        rfl

theorem cell23_1777996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_1777996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1777996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1777996 prefixEnd_1777996 := by exact prefixLift 1777996
  have htrace : WordTrace (prefixWord ++ tailWord_1777996) baseStart_1777996 baseEnd_1777996 := by
    simpa [prefixWord, tailWord_1777996, baseEnd_1777996] using wordTrace_append hprefix tailTrace_1777996
  have hstable : (prefixWord ++ tailWord_1777996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1777996).length < 2 ^ (prefixWord ++ tailWord_1777996).sum := by decide
  have hdescent : baseEnd_1777996 < baseStart_1777996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1777996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778023 : List Nat := [1, 1, 5, 1, 3, 2, 1, 1, 1, 3, 4]
def baseStart_1778023 : Nat := 118140960795 + 1778023 * 2 ^ 59
def prefixEnd_1778023 : Nat := 4983230072969 + 3 ^ 40 * 1778023 * 2
def baseEnd_1778023 : Nat := 912980413749202210535527

theorem tailTrace_1778023 : CollatzResearch.WordTrace tailWord_1778023 prefixEnd_1778023 912980413749202210535527 := by
  unfold tailWord_1778023
  simp only [CollatzResearch.WordTrace]
  refine ⟨64849826437533807997730723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43233217625022538665153815 64849826437533807997730723)
  ·
    refine ⟨97274739656300711996596085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64849826437533807997730723 97274739656300711996596085)
    ·
      refine ⟨9119506842778191749680883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97274739656300711996596085 9119506842778191749680883)
      ·
        refine ⟨13679260264167287624521325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9119506842778191749680883 13679260264167287624521325)
        ·
          refine ⟨5129722599062732859195497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13679260264167287624521325 5129722599062732859195497)
          ·
            refine ⟨3847291949297049644396623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5129722599062732859195497 3847291949297049644396623)
            ·
              refine ⟨5770937923945574466594935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3847291949297049644396623 5770937923945574466594935)
              ·
                refine ⟨8656406885918361699892403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5770937923945574466594935 8656406885918361699892403)
                ·
                  refine ⟨12984610328877542549838605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8656406885918361699892403 12984610328877542549838605)
                  ·
                    refine ⟨4869228873329078456189477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12984610328877542549838605 4869228873329078456189477)
                    ·
                      refine ⟨912980413749202210535527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4869228873329078456189477 912980413749202210535527)
                      ·
                        rfl

theorem cell23_1778023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_1778023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1778023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1778023 prefixEnd_1778023 := by exact prefixLift 1778023
  have htrace : WordTrace (prefixWord ++ tailWord_1778023) baseStart_1778023 baseEnd_1778023 := by
    simpa [prefixWord, tailWord_1778023, baseEnd_1778023] using wordTrace_append hprefix tailTrace_1778023
  have hstable : (prefixWord ++ tailWord_1778023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778023).length < 2 ^ (prefixWord ++ tailWord_1778023).sum := by decide
  have hdescent : baseEnd_1778023 < baseStart_1778023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778096 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 4]
def baseStart_1778096 : Nat := 118140960795 + 1778096 * 2 ^ 59
def prefixEnd_1778096 : Nat := 4983230072969 + 3 ^ 40 * 1778096 * 2
def baseEnd_1778096 : Nat := 913017897836980424922691

theorem tailTrace_1778096 : CollatzResearch.WordTrace tailWord_1778096 prefixEnd_1778096 913017897836980424922691 := by
  unfold tailWord_1778096
  simp only [CollatzResearch.WordTrace]
  refine ⟨32426244483134670732569071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43234992644179560976758761 32426244483134670732569071)
  ·
    refine ⟨48639366724702006098853607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32426244483134670732569071 48639366724702006098853607)
    ·
      refine ⟨72959050087053009148280411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48639366724702006098853607 72959050087053009148280411)
      ·
        refine ⟨109438575130579513722420617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72959050087053009148280411 109438575130579513722420617)
        ·
          refine ⟨82078931347934635291815463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109438575130579513722420617 82078931347934635291815463)
          ·
            refine ⟨123118397021901952937723195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82078931347934635291815463 123118397021901952937723195)
            ·
              refine ⟨184677595532852929406584793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123118397021901952937723195 184677595532852929406584793)
              ·
                refine ⟨138508196649639697054938595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184677595532852929406584793 138508196649639697054938595)
                ·
                  refine ⟨207762294974459545582407893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138508196649639697054938595 207762294974459545582407893)
                  ·
                    refine ⟨4869428788463895599587685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 207762294974459545582407893 4869428788463895599587685)
                    ·
                      refine ⟨913017897836980424922691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4869428788463895599587685 913017897836980424922691)
                      ·
                        rfl

theorem cell23_1778096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 4].length) (baseStart_1778096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1778096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1778096 prefixEnd_1778096 := by exact prefixLift 1778096
  have htrace : WordTrace (prefixWord ++ tailWord_1778096) baseStart_1778096 baseEnd_1778096 := by
    simpa [prefixWord, tailWord_1778096, baseEnd_1778096] using wordTrace_append hprefix tailTrace_1778096
  have hstable : (prefixWord ++ tailWord_1778096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778096).length < 2 ^ (prefixWord ++ tailWord_1778096).sum := by decide
  have hdescent : baseEnd_1778096 < baseStart_1778096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778134 : List Nat := [5, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2]
def baseStart_1778134 : Nat := 118140960795 + 1778134 * 2 ^ 59
def prefixEnd_1778134 : Nat := 4983230072969 + 3 ^ 40 * 1778134 * 2
def baseEnd_1778134 : Nat := 913037410101851276247517

theorem tailTrace_1778134 : CollatzResearch.WordTrace tailWord_1778134 prefixEnd_1778134 913037410101851276247517 := by
  unfold tailWord_1778134
  simp only [CollatzResearch.WordTrace]
  refine ⟨4053367183758229622188841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43235916626754449303347637 4053367183758229622188841)
  ·
    refine ⟨3040025387818672216641631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4053367183758229622188841 3040025387818672216641631)
    ·
      refine ⟨4560038081728008324962447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3040025387818672216641631 4560038081728008324962447)
      ·
        refine ⟨6840057122592012487443671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4560038081728008324962447 6840057122592012487443671)
        ·
          refine ⟨10260085683888018731165507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6840057122592012487443671 10260085683888018731165507)
          ·
            refine ⟨15390128525832028096748261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10260085683888018731165507 15390128525832028096748261)
            ·
              refine ⟨2885649098593505268140299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15390128525832028096748261 2885649098593505268140299)
              ·
                refine ⟨4328473647890257902210449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2885649098593505268140299 4328473647890257902210449)
                ·
                  refine ⟨3246355235917693426657837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4328473647890257902210449 3246355235917693426657837)
                  ·
                    refine ⟨1217383213469135034996689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3246355235917693426657837 1217383213469135034996689)
                    ·
                      refine ⟨913037410101851276247517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1217383213469135034996689 913037410101851276247517)
                      ·
                        rfl

theorem cell23_1778134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_1778134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1778134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1778134 prefixEnd_1778134 := by exact prefixLift 1778134
  have htrace : WordTrace (prefixWord ++ tailWord_1778134) baseStart_1778134 baseEnd_1778134 := by
    simpa [prefixWord, tailWord_1778134, baseEnd_1778134] using wordTrace_append hprefix tailTrace_1778134
  have hstable : (prefixWord ++ tailWord_1778134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778134).length < 2 ^ (prefixWord ++ tailWord_1778134).sum := by decide
  have hdescent : baseEnd_1778134 < baseStart_1778134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778143 : List Nat := [1, 1, 2, 3, 3, 2, 1, 1, 3, 2, 4]
def baseStart_1778143 : Nat := 118140960795 + 1778143 * 2 ^ 59
def prefixEnd_1778143 : Nat := 4983230072969 + 3 ^ 40 * 1778143 * 2
def baseEnd_1778143 : Nat := 913042031427741741034975

theorem tailTrace_1778143 : CollatzResearch.WordTrace tailWord_1778143 prefixEnd_1778143 913042031427741741034975 := by
  unfold tailWord_1778143
  simp only [CollatzResearch.WordTrace]
  refine ⟨64854203197099068492099083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43236135464732712328066055 64854203197099068492099083)
  ·
    refine ⟨97281304795648602738148625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64854203197099068492099083 97281304795648602738148625)
    ·
      refine ⟨72960978596736452053611469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97281304795648602738148625 72960978596736452053611469)
      ·
        refine ⟨27360366973776169520104301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72960978596736452053611469 27360366973776169520104301)
        ·
          refine ⟨10260137615166063570039113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27360366973776169520104301 10260137615166063570039113)
          ·
            refine ⟨7695103211374547677529335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10260137615166063570039113 7695103211374547677529335)
            ·
              refine ⟨11542654817061821516294003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7695103211374547677529335 11542654817061821516294003)
              ·
                refine ⟨17313982225592732274441005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11542654817061821516294003 17313982225592732274441005)
                ·
                  refine ⟨6492743334597274602915377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17313982225592732274441005 6492743334597274602915377)
                  ·
                    refine ⟨4869557500947955952186533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6492743334597274602915377 4869557500947955952186533)
                    ·
                      refine ⟨913042031427741741034975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4869557500947955952186533 913042031427741741034975)
                      ·
                        rfl

theorem cell23_1778143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_1778143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1778143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1778143 prefixEnd_1778143 := by exact prefixLift 1778143
  have htrace : WordTrace (prefixWord ++ tailWord_1778143) baseStart_1778143 baseEnd_1778143 := by
    simpa [prefixWord, tailWord_1778143, baseEnd_1778143] using wordTrace_append hprefix tailTrace_1778143
  have hstable : (prefixWord ++ tailWord_1778143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778143).length < 2 ^ (prefixWord ++ tailWord_1778143).sum := by decide
  have hdescent : baseEnd_1778143 < baseStart_1778143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778157 : List Nat := [1, 5, 1, 3, 1, 1, 1, 4, 2, 4]
def baseStart_1778157 : Nat := 118140960795 + 1778157 * 2 ^ 59
def prefixEnd_1778157 : Nat := 4983230072969 + 3 ^ 40 * 1778157 * 2
def baseEnd_1778157 : Nat := 304349740052301562086637

theorem tailTrace_1778157 : CollatzResearch.WordTrace tailWord_1778157 prefixEnd_1778157 304349740052301562086637 := by
  unfold tailWord_1778157
  simp only [CollatzResearch.WordTrace]
  refine ⟨64854713819048348883108725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43236475879365565922072483 64854713819048348883108725)
  ·
    refine ⟨6080129420535782707791443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64854713819048348883108725 6080129420535782707791443)
    ·
      refine ⟨9120194130803674061687165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6080129420535782707791443 9120194130803674061687165)
      ·
        refine ⟨3420072799051377773132687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9120194130803674061687165 3420072799051377773132687)
        ·
          refine ⟨5130109198577066659699031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3420072799051377773132687 5130109198577066659699031)
          ·
            refine ⟨7695163797865599989548547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5130109198577066659699031 7695163797865599989548547)
            ·
              refine ⟨11542745696798399984322821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7695163797865599989548547 11542745696798399984322821)
              ·
                refine ⟨2164264818149699997060529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11542745696798399984322821 2164264818149699997060529)
                ·
                  refine ⟨1623198613612274997795397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2164264818149699997060529 1623198613612274997795397)
                  ·
                    refine ⟨304349740052301562086637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1623198613612274997795397 304349740052301562086637)
                    ·
                      rfl

theorem cell23_1778157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_1778157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1778157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1778157 prefixEnd_1778157 := by exact prefixLift 1778157
  have htrace : WordTrace (prefixWord ++ tailWord_1778157) baseStart_1778157 baseEnd_1778157 := by
    simpa [prefixWord, tailWord_1778157, baseEnd_1778157] using wordTrace_append hprefix tailTrace_1778157
  have hstable : (prefixWord ++ tailWord_1778157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778157).length < 2 ^ (prefixWord ++ tailWord_1778157).sum := by decide
  have hdescent : baseEnd_1778157 < baseStart_1778157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778163 : List Nat := [1, 1, 1, 2, 2, 2, 3, 2, 3, 3, 3]
def baseStart_1778163 : Nat := 118140960795 + 1778163 * 2 ^ 59
def prefixEnd_1778163 : Nat := 4983230072969 + 3 ^ 40 * 1778163 * 2
def baseEnd_1778163 : Nat := 913052301040831662784883

theorem tailTrace_1778163 : CollatzResearch.WordTrace tailWord_1778163 prefixEnd_1778163 913052301040831662784883 := by
  unfold tailWord_1778163
  simp only [CollatzResearch.WordTrace]
  refine ⟨64854932657026611907827143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43236621771351074605218095 64854932657026611907827143)
  ·
    refine ⟨97282398985539917861740715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64854932657026611907827143 97282398985539917861740715)
    ·
      refine ⟨145923598478309876792611073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97282398985539917861740715 145923598478309876792611073)
      ·
        refine ⟨109442698858732407594458305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145923598478309876792611073 109442698858732407594458305)
        ·
          refine ⟨82082024144049305695843729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109442698858732407594458305 82082024144049305695843729)
          ·
            refine ⟨61561518108036979271882797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82082024144049305695843729 61561518108036979271882797)
            ·
              refine ⟨23085569290513867226956049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61561518108036979271882797 23085569290513867226956049)
              ·
                refine ⟨17314176967885400420217037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23085569290513867226956049 17314176967885400420217037)
                ·
                  refine ⟨6492816362957025157581389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17314176967885400420217037 6492816362957025157581389)
                  ·
                    refine ⟨2434806136108884434093021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6492816362957025157581389 2434806136108884434093021)
                    ·
                      refine ⟨913052301040831662784883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2434806136108884434093021 913052301040831662784883)
                      ·
                        rfl

theorem cell23_1778163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3, 3, 3].length) (baseStart_1778163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1778163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1778163 prefixEnd_1778163 := by exact prefixLift 1778163
  have htrace : WordTrace (prefixWord ++ tailWord_1778163) baseStart_1778163 baseEnd_1778163 := by
    simpa [prefixWord, tailWord_1778163, baseEnd_1778163] using wordTrace_append hprefix tailTrace_1778163
  have hstable : (prefixWord ++ tailWord_1778163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778163).length < 2 ^ (prefixWord ++ tailWord_1778163).sum := by decide
  have hdescent : baseEnd_1778163 < baseStart_1778163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778213 : List Nat := [1, 3, 1, 2, 2, 1, 3, 2, 2, 6]
def baseStart_1778213 : Nat := 118140960795 + 1778213 * 2 ^ 59
def prefixEnd_1778213 : Nat := 4983230072969 + 3 ^ 40 * 1778213 * 2
def baseEnd_1778213 : Nat := 304359325024518822386551

theorem tailTrace_1778213 : CollatzResearch.WordTrace tailWord_1778213 prefixEnd_1778213 304359325024518822386551 := by
  unfold tailWord_1778213
  simp only [CollatzResearch.WordTrace]
  refine ⟨64856756306845470447147293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43237837537896980298098195 64856756306845470447147293)
  ·
    refine ⟨24321283615067051417680235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64856756306845470447147293 24321283615067051417680235)
    ·
      refine ⟨36481925422600577126520353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24321283615067051417680235 36481925422600577126520353)
      ·
        refine ⟨27361444066950432844890265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36481925422600577126520353 27361444066950432844890265)
        ·
          refine ⟨20521083050212824633667699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27361444066950432844890265 20521083050212824633667699)
          ·
            refine ⟨30781624575319236950501549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20521083050212824633667699 30781624575319236950501549)
            ·
              refine ⟨11543109215744713856438081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30781624575319236950501549 11543109215744713856438081)
              ·
                refine ⟨8657331911808535392328561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11543109215744713856438081 8657331911808535392328561)
                ·
                  refine ⟨6492998933856401544246421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8657331911808535392328561 6492998933856401544246421)
                  ·
                    refine ⟨304359325024518822386551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6492998933856401544246421 304359325024518822386551)
                    ·
                      rfl

theorem cell23_1778213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2, 6].length) (baseStart_1778213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1778213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1778213 prefixEnd_1778213 := by exact prefixLift 1778213
  have htrace : WordTrace (prefixWord ++ tailWord_1778213) baseStart_1778213 baseEnd_1778213 := by
    simpa [prefixWord, tailWord_1778213, baseEnd_1778213] using wordTrace_append hprefix tailTrace_1778213
  have hstable : (prefixWord ++ tailWord_1778213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778213).length < 2 ^ (prefixWord ++ tailWord_1778213).sum := by decide
  have hdescent : baseEnd_1778213 < baseStart_1778213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778220 : List Nat := [2, 2, 1, 1, 1, 2, 1, 4, 3, 4, 2]
def baseStart_1778220 : Nat := 118140960795 + 1778220 * 2 ^ 59
def prefixEnd_1778220 : Nat := 4983230072969 + 3 ^ 40 * 1778220 * 2
def baseEnd_1778220 : Nat := 913081569438137939772121

theorem tailTrace_1778220 : CollatzResearch.WordTrace tailWord_1778220 prefixEnd_1778220 913081569438137939772121 := by
  unfold tailWord_1778220
  simp only [CollatzResearch.WordTrace]
  refine ⟨32428505808910055321326057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43238007745213407095101409 32428505808910055321326057)
  ·
    refine ⟨24321379356682541490994543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32428505808910055321326057 24321379356682541490994543)
    ·
      refine ⟨36482069035023812236491815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24321379356682541490994543 36482069035023812236491815)
      ·
        refine ⟨54723103552535718354737723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36482069035023812236491815 54723103552535718354737723)
        ·
          refine ⟨82084655328803577532106585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54723103552535718354737723 82084655328803577532106585)
          ·
            refine ⟨61563491496602683149079939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82084655328803577532106585 61563491496602683149079939)
            ·
              refine ⟨92345237244904024723619909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61563491496602683149079939 92345237244904024723619909)
              ·
                refine ⟨17314731983419504635678733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92345237244904024723619909 17314731983419504635678733)
                ·
                  refine ⟨6493024493782314238379525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17314731983419504635678733 6493024493782314238379525)
                  ·
                    refine ⟨1217442092584183919696161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6493024493782314238379525 1217442092584183919696161)
                    ·
                      refine ⟨913081569438137939772121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1217442092584183919696161 913081569438137939772121)
                      ·
                        rfl

theorem cell23_1778220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 4, 2].length) (baseStart_1778220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1778220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1778220 prefixEnd_1778220 := by exact prefixLift 1778220
  have htrace : WordTrace (prefixWord ++ tailWord_1778220) baseStart_1778220 baseEnd_1778220 := by
    simpa [prefixWord, tailWord_1778220, baseEnd_1778220] using wordTrace_append hprefix tailTrace_1778220
  have hstable : (prefixWord ++ tailWord_1778220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778220).length < 2 ^ (prefixWord ++ tailWord_1778220).sum := by decide
  have hdescent : baseEnd_1778220 < baseStart_1778220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778277 : List Nat := [1, 3, 1, 3, 4, 2, 1, 1, 7]
def baseStart_1778277 : Nat := 118140960795 + 1778277 * 2 ^ 59
def prefixEnd_1778277 : Nat := 4983230072969 + 3 ^ 40 * 1778277 * 2
def baseEnd_1778277 : Nat := 101456759759493801862151

theorem tailTrace_1778277 : CollatzResearch.WordTrace tailWord_1778277 prefixEnd_1778277 101456759759493801862151 := by
  unfold tailWord_1778277
  simp only [CollatzResearch.WordTrace]
  refine ⟨64859090578613609377477085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43239393719075739584984723 64859090578613609377477085)
  ·
    refine ⟨24322158966980103516553907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64859090578613609377477085 24322158966980103516553907)
    ·
      refine ⟨36483238450470155274830861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24322158966980103516553907 36483238450470155274830861)
      ·
        refine ⟨13681214418926308228061573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36483238450470155274830861 13681214418926308228061573)
        ·
          refine ⟨2565227703548682792761545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13681214418926308228061573 2565227703548682792761545)
          ·
            refine ⟨1923920777661512094571159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2565227703548682792761545 1923920777661512094571159)
            ·
              refine ⟨2885881166492268141856739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1923920777661512094571159 2885881166492268141856739)
              ·
                refine ⟨4328821749738402212785109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2885881166492268141856739 4328821749738402212785109)
                ·
                  refine ⟨101456759759493801862151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4328821749738402212785109 101456759759493801862151)
                  ·
                    rfl

theorem cell23_1778277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 1, 7].length) (baseStart_1778277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1778277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1778277 prefixEnd_1778277 := by exact prefixLift 1778277
  have htrace : WordTrace (prefixWord ++ tailWord_1778277) baseStart_1778277 baseEnd_1778277 := by
    simpa [prefixWord, tailWord_1778277, baseEnd_1778277] using wordTrace_append hprefix tailTrace_1778277
  have hstable : (prefixWord ++ tailWord_1778277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778277).length < 2 ^ (prefixWord ++ tailWord_1778277).sum := by decide
  have hdescent : baseEnd_1778277 < baseStart_1778277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778288 : List Nat := [2, 1, 1, 1, 7, 2, 2, 1, 2, 2, 2]
def baseStart_1778288 : Nat := 118140960795 + 1778288 * 2 ^ 59
def prefixEnd_1778288 : Nat := 4983230072969 + 3 ^ 40 * 1778288 * 2
def baseEnd_1778288 : Nat := 913116486122643673721809

theorem tailTrace_1778288 : CollatzResearch.WordTrace tailWord_1778288 prefixEnd_1778288 913116486122643673721809 := by
  unfold tailWord_1778288
  simp only [CollatzResearch.WordTrace]
  refine ⟨32429745890786879128063759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43239661187715838837418345 32429745890786879128063759)
  ·
    refine ⟨48644618836180318692095639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32429745890786879128063759 48644618836180318692095639)
    ·
      refine ⟨72966928254270478038143459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48644618836180318692095639 72966928254270478038143459)
      ·
        refine ⟨109450392381405717057215189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72966928254270478038143459 109450392381405717057215189)
        ·
          refine ⟨2565243571439196493528481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 109450392381405717057215189 2565243571439196493528481)
          ·
            refine ⟨1923932678579397370146361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2565243571439196493528481 1923932678579397370146361)
            ·
              refine ⟨1442949508934548027609771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1923932678579397370146361 1442949508934548027609771)
              ·
                refine ⟨2164424263401822041414657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1442949508934548027609771 2164424263401822041414657)
                ·
                  refine ⟨1623318197551366531060993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2164424263401822041414657 1623318197551366531060993)
                  ·
                    refine ⟨1217488648163524898295745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1623318197551366531060993 1217488648163524898295745)
                    ·
                      refine ⟨913116486122643673721809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1217488648163524898295745 913116486122643673721809)
                      ·
                        rfl

theorem cell23_1778288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 1, 2, 2, 2].length) (baseStart_1778288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1778288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1778288 prefixEnd_1778288 := by exact prefixLift 1778288
  have htrace : WordTrace (prefixWord ++ tailWord_1778288) baseStart_1778288 baseEnd_1778288 := by
    simpa [prefixWord, tailWord_1778288, baseEnd_1778288] using wordTrace_append hprefix tailTrace_1778288
  have hstable : (prefixWord ++ tailWord_1778288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778288).length < 2 ^ (prefixWord ++ tailWord_1778288).sum := by decide
  have hdescent : baseEnd_1778288 < baseStart_1778288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778323 : List Nat := [1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 6]
def baseStart_1778323 : Nat := 118140960795 + 1778323 * 2 ^ 59
def prefixEnd_1778323 : Nat := 4983230072969 + 3 ^ 40 * 1778323 * 2
def baseEnd_1778323 : Nat := 913134457945551036784147

theorem tailTrace_1778323 : CollatzResearch.WordTrace tailWord_1778323 prefixEnd_1778323 913134457945551036784147 := by
  unfold tailWord_1778323
  simp only [CollatzResearch.WordTrace]
  refine ⟨64860768336446959233651623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43240512224297972822434415 64860768336446959233651623)
  ·
    refine ⟨97291152504670438850477435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64860768336446959233651623 97291152504670438850477435)
    ·
      refine ⟨145936728757005658275716153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97291152504670438850477435 145936728757005658275716153)
      ·
        refine ⟨109452546567754243706787115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145936728757005658275716153 109452546567754243706787115)
        ·
          refine ⟨164178819851631365560180673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109452546567754243706787115 164178819851631365560180673)
          ·
            refine ⟨123134114888723524170135505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164178819851631365560180673 123134114888723524170135505)
            ·
              refine ⟨92350586166542643127601629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123134114888723524170135505 92350586166542643127601629)
              ·
                refine ⟨34631469812453491172850611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92350586166542643127601629 34631469812453491172850611)
                ·
                  refine ⟨51947204718680236759275917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34631469812453491172850611 51947204718680236759275917)
                  ·
                    refine ⟨19480201769505088784728469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51947204718680236759275917 19480201769505088784728469)
                    ·
                      refine ⟨913134457945551036784147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19480201769505088784728469 913134457945551036784147)
                      ·
                        rfl

theorem cell23_1778323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 6].length) (baseStart_1778323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1778323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1778323 prefixEnd_1778323 := by exact prefixLift 1778323
  have htrace : WordTrace (prefixWord ++ tailWord_1778323) baseStart_1778323 baseEnd_1778323 := by
    simpa [prefixWord, tailWord_1778323, baseEnd_1778323] using wordTrace_append hprefix tailTrace_1778323
  have hstable : (prefixWord ++ tailWord_1778323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778323).length < 2 ^ (prefixWord ++ tailWord_1778323).sum := by decide
  have hdescent : baseEnd_1778323 < baseStart_1778323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778327 : List Nat := [1, 1, 3, 3, 2, 1, 2, 2, 2, 4, 2]
def baseStart_1778327 : Nat := 118140960795 + 1778327 * 2 ^ 59
def prefixEnd_1778327 : Nat := 4983230072969 + 3 ^ 40 * 1778327 * 2
def baseEnd_1778327 : Nat := 913136511868169021134129

theorem tailTrace_1778327 : CollatzResearch.WordTrace tailWord_1778327 prefixEnd_1778327 913136511868169021134129 := by
  unfold tailWord_1778327
  simp only [CollatzResearch.WordTrace]
  refine ⟨64860914228432467916797235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43240609485621645277864823 64860914228432467916797235)
  ·
    refine ⟨97291371342648701875195853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64860914228432467916797235 97291371342648701875195853)
    ·
      refine ⟨36484264253493263203198445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97291371342648701875195853 36484264253493263203198445)
      ·
        refine ⟨13681599095059973701199417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36484264253493263203198445 13681599095059973701199417)
        ·
          refine ⟨10261199321294980275899563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13681599095059973701199417 10261199321294980275899563)
          ·
            refine ⟨15391798981942470413849345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10261199321294980275899563 15391798981942470413849345)
            ·
              refine ⟨11543849236456852810387009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15391798981942470413849345 11543849236456852810387009)
              ·
                refine ⟨8657886927342639607790257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11543849236456852810387009 8657886927342639607790257)
                ·
                  refine ⟨6493415195506979705842693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8657886927342639607790257 6493415195506979705842693)
                  ·
                    refine ⟨1217515349157558694845505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6493415195506979705842693 1217515349157558694845505)
                    ·
                      refine ⟨913136511868169021134129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1217515349157558694845505 913136511868169021134129)
                      ·
                        rfl

theorem cell23_1778327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2, 4, 2].length) (baseStart_1778327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1778327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1778327 prefixEnd_1778327 := by exact prefixLift 1778327
  have htrace : WordTrace (prefixWord ++ tailWord_1778327) baseStart_1778327 baseEnd_1778327 := by
    simpa [prefixWord, tailWord_1778327, baseEnd_1778327] using wordTrace_append hprefix tailTrace_1778327
  have hstable : (prefixWord ++ tailWord_1778327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778327).length < 2 ^ (prefixWord ++ tailWord_1778327).sum := by decide
  have hdescent : baseEnd_1778327 < baseStart_1778327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778358 : List Nat := [5, 1, 3, 1, 3, 1, 1, 1, 2, 5]
def baseStart_1778358 : Nat := 118140960795 + 1778358 * 2 ^ 59
def prefixEnd_1778358 : Nat := 4983230072969 + 3 ^ 40 * 1778358 * 2
def baseEnd_1778358 : Nat := 304384143256152799948829

theorem tailTrace_1778358 : CollatzResearch.WordTrace tailWord_1778358 prefixEnd_1778358 304384143256152799948829 := by
  unfold tailWord_1778358
  simp only [CollatzResearch.WordTrace]
  refine ⟨4053877805707510013198483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43241363260880106807450485 4053877805707510013198483)
  ·
    refine ⟨6080816708561265019797725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4053877805707510013198483 6080816708561265019797725)
    ·
      refine ⟨2280306265710474382424147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6080816708561265019797725 2280306265710474382424147)
      ·
        refine ⟨3420459398565711573636221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2280306265710474382424147 3420459398565711573636221)
        ·
          refine ⟨1282672274462141840113583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3420459398565711573636221 1282672274462141840113583)
          ·
            refine ⟨1924008411693212760170375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1282672274462141840113583 1924008411693212760170375)
            ·
              refine ⟨2886012617539819140255563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1924008411693212760170375 2886012617539819140255563)
              ·
                refine ⟨4329018926309728710383345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2886012617539819140255563 4329018926309728710383345)
                ·
                  refine ⟨3246764194732296532787509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4329018926309728710383345 3246764194732296532787509)
                  ·
                    refine ⟨304384143256152799948829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3246764194732296532787509 304384143256152799948829)
                    ·
                      rfl

theorem cell23_1778358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_1778358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1778358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1778358 prefixEnd_1778358 := by exact prefixLift 1778358
  have htrace : WordTrace (prefixWord ++ tailWord_1778358) baseStart_1778358 baseEnd_1778358 := by
    simpa [prefixWord, tailWord_1778358, baseEnd_1778358] using wordTrace_append hprefix tailTrace_1778358
  have hstable : (prefixWord ++ tailWord_1778358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778358).length < 2 ^ (prefixWord ++ tailWord_1778358).sum := by decide
  have hdescent : baseEnd_1778358 < baseStart_1778358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778394 : List Nat := [3, 1, 1, 2, 2, 2, 4, 1, 3, 1, 3]
def baseStart_1778394 : Nat := 118140960795 + 1778394 * 2 ^ 59
def prefixEnd_1778394 : Nat := 4983230072969 + 3 ^ 40 * 1778394 * 2
def baseEnd_1778394 : Nat := 913170915072020258996321

theorem tailTrace_1778394 : CollatzResearch.WordTrace tailWord_1778394 prefixEnd_1778394 913170915072020258996321 := by
  unfold tailWord_1778394
  simp only [CollatzResearch.WordTrace]
  refine ⟨16215839479797434589871559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43242238612793158906324157 16215839479797434589871559)
  ·
    refine ⟨24323759219696151884807339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16215839479797434589871559 24323759219696151884807339)
    ·
      refine ⟨36485638829544227827211009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24323759219696151884807339 36485638829544227827211009)
      ·
        refine ⟨27364229122158170870408257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36485638829544227827211009 27364229122158170870408257)
        ·
          refine ⟨20523171841618628152806193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27364229122158170870408257 20523171841618628152806193)
          ·
            refine ⟨15392378881213971114604645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20523171841618628152806193 15392378881213971114604645)
            ·
              refine ⟨2886071040227619583988371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15392378881213971114604645 2886071040227619583988371)
              ·
                refine ⟨4329106560341429375982557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2886071040227619583988371 4329106560341429375982557)
                ·
                  refine ⟨1623414960128036015993459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4329106560341429375982557 1623414960128036015993459)
                  ·
                    refine ⟨2435122440192054023990189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1623414960128036015993459 2435122440192054023990189)
                    ·
                      refine ⟨913170915072020258996321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2435122440192054023990189 913170915072020258996321)
                      ·
                        rfl

theorem cell23_1778394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 1, 3, 1, 3].length) (baseStart_1778394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1778394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1778394 prefixEnd_1778394 := by exact prefixLift 1778394
  have htrace : WordTrace (prefixWord ++ tailWord_1778394) baseStart_1778394 baseEnd_1778394 := by
    simpa [prefixWord, tailWord_1778394, baseEnd_1778394] using wordTrace_append hprefix tailTrace_1778394
  have hstable : (prefixWord ++ tailWord_1778394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778394).length < 2 ^ (prefixWord ++ tailWord_1778394).sum := by decide
  have hdescent : baseEnd_1778394 < baseStart_1778394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778414 : List Nat := [4, 1, 2, 1, 1, 4, 2, 2, 1, 5]
def baseStart_1778414 : Nat := 118140960795 + 1778414 * 2 ^ 59
def prefixEnd_1778414 : Nat := 4983230072969 + 3 ^ 40 * 1778414 * 2
def baseEnd_1778414 : Nat := 304393728228370060248743

theorem tailTrace_1778414 : CollatzResearch.WordTrace tailWord_1778414 prefixEnd_1778414 304393728228370060248743 := by
  unfold tailWord_1778414
  simp only [CollatzResearch.WordTrace]
  refine ⟨8108010922389660221901787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43242724919411521183476197 8108010922389660221901787)
  ·
    refine ⟨12162016383584490332852681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8108010922389660221901787 12162016383584490332852681)
    ·
      refine ⟨9121512287688367749639511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12162016383584490332852681 9121512287688367749639511)
      ·
        refine ⟨13682268431532551624459267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9121512287688367749639511 13682268431532551624459267)
        ·
          refine ⟨20523402647298827436688901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13682268431532551624459267 20523402647298827436688901)
          ·
            refine ⟨3848137996368530144379169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20523402647298827436688901 3848137996368530144379169)
            ·
              refine ⟨2886103497276397608284377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3848137996368530144379169 2886103497276397608284377)
              ·
                refine ⟨2164577622957298206213283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2886103497276397608284377 2164577622957298206213283)
                ·
                  refine ⟨3246866434435947309319925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2164577622957298206213283 3246866434435947309319925)
                  ·
                    refine ⟨304393728228370060248743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3246866434435947309319925 304393728228370060248743)
                    ·
                      rfl

theorem cell23_1778414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_1778414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1778414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1778414 prefixEnd_1778414 := by exact prefixLift 1778414
  have htrace : WordTrace (prefixWord ++ tailWord_1778414) baseStart_1778414 baseEnd_1778414 := by
    simpa [prefixWord, tailWord_1778414, baseEnd_1778414] using wordTrace_append hprefix tailTrace_1778414
  have hstable : (prefixWord ++ tailWord_1778414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778414).length < 2 ^ (prefixWord ++ tailWord_1778414).sum := by decide
  have hdescent : baseEnd_1778414 < baseStart_1778414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778417 : List Nat := [1, 2, 2, 2, 2, 2, 1, 1, 2, 6, 2]
def baseStart_1778417 : Nat := 118140960795 + 1778417 * 2 ^ 59
def prefixEnd_1778417 : Nat := 4983230072969 + 3 ^ 40 * 1778417 * 2
def baseEnd_1778417 : Nat := 913182725127073669008715

theorem tailTrace_1778417 : CollatzResearch.WordTrace tailWord_1778417 prefixEnd_1778417 913182725127073669008715 := by
  unfold tailWord_1778417
  simp only [CollatzResearch.WordTrace]
  refine ⟨64864196798106413287573505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43242797865404275525049003 64864196798106413287573505)
  ·
    refine ⟨48648147598579809965680129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64864196798106413287573505 48648147598579809965680129)
    ·
      refine ⟨36486110698934857474260097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48648147598579809965680129 36486110698934857474260097)
      ·
        refine ⟨27364583024201143105695073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36486110698934857474260097 27364583024201143105695073)
        ·
          refine ⟨20523437268150857329271305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27364583024201143105695073 20523437268150857329271305)
          ·
            refine ⟨15392577951113142996953479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20523437268150857329271305 15392577951113142996953479)
            ·
              refine ⟨23088866926669714495430219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15392577951113142996953479 23088866926669714495430219)
              ·
                refine ⟨34633300390004571743145329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23088866926669714495430219 34633300390004571743145329)
                ·
                  refine ⟨25974975292503428807358997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34633300390004571743145329 25974975292503428807358997)
                  ·
                    refine ⟨1217576966836098225344953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25974975292503428807358997 1217576966836098225344953)
                    ·
                      refine ⟨913182725127073669008715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1217576966836098225344953 913182725127073669008715)
                      ·
                        rfl

theorem cell23_1778417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 6, 2].length) (baseStart_1778417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1778417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1778417 prefixEnd_1778417 := by exact prefixLift 1778417
  have htrace : WordTrace (prefixWord ++ tailWord_1778417) baseStart_1778417 baseEnd_1778417 := by
    simpa [prefixWord, tailWord_1778417, baseEnd_1778417] using wordTrace_append hprefix tailTrace_1778417
  have hstable : (prefixWord ++ tailWord_1778417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778417).length < 2 ^ (prefixWord ++ tailWord_1778417).sum := by decide
  have hdescent : baseEnd_1778417 < baseStart_1778417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778428 : List Nat := [2, 2, 2, 1, 3, 4, 1, 3, 1, 1, 3]
def baseStart_1778428 : Nat := 118140960795 + 1778428 * 2 ^ 59
def prefixEnd_1778428 : Nat := 4983230072969 + 3 ^ 40 * 1778428 * 2
def baseEnd_1778428 : Nat := 913188373414273125971165

theorem tailTrace_1778428 : CollatzResearch.WordTrace tailWord_1778428 prefixEnd_1778428 913188373414273125971165 := by
  unfold tailWord_1778428
  simp only [CollatzResearch.WordTrace]
  refine ⟨32432299000533281083111969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43243065334044374777482625 32432299000533281083111969)
  ·
    refine ⟨24324224250399960812333977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32432299000533281083111969 24324224250399960812333977)
    ·
      refine ⟨18243168187799970609250483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24324224250399960812333977 18243168187799970609250483)
      ·
        refine ⟨27364752281699955913875725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18243168187799970609250483 27364752281699955913875725)
        ·
          refine ⟨10261782105637483467703397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27364752281699955913875725 10261782105637483467703397)
          ·
            refine ⟨1924084144807028150194387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10261782105637483467703397 1924084144807028150194387)
            ·
              refine ⟨2886126217210542225291581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1924084144807028150194387 2886126217210542225291581)
              ·
                refine ⟨1082297331453953334484343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2886126217210542225291581 1082297331453953334484343)
                ·
                  refine ⟨1623445997180930001726515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1082297331453953334484343 1623445997180930001726515)
                  ·
                    refine ⟨2435168995771395002589773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1623445997180930001726515 2435168995771395002589773)
                    ·
                      refine ⟨913188373414273125971165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2435168995771395002589773 913188373414273125971165)
                      ·
                        rfl

theorem cell23_1778428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 3, 1, 1, 3].length) (baseStart_1778428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1778428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1778428 prefixEnd_1778428 := by exact prefixLift 1778428
  have htrace : WordTrace (prefixWord ++ tailWord_1778428) baseStart_1778428 baseEnd_1778428 := by
    simpa [prefixWord, tailWord_1778428, baseEnd_1778428] using wordTrace_append hprefix tailTrace_1778428
  have hstable : (prefixWord ++ tailWord_1778428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778428).length < 2 ^ (prefixWord ++ tailWord_1778428).sum := by decide
  have hdescent : baseEnd_1778428 < baseStart_1778428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778440 : List Nat := [2, 1, 3, 2, 2, 2, 11]
def baseStart_1778440 : Nat := 118140960795 + 1778440 * 2 ^ 59
def prefixEnd_1778440 : Nat := 4983230072969 + 3 ^ 40 * 1778440 * 2
def baseEnd_1778440 : Nat := 11274006607186754061989

theorem tailTrace_1778440 : CollatzResearch.WordTrace tailWord_1778440 prefixEnd_1778440 11274006607186754061989 := by
  unfold tailWord_1778440
  simp only [CollatzResearch.WordTrace]
  refine ⟨32432517838511544107830387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43243357118015392143773849 32432517838511544107830387)
  ·
    refine ⟨48648776757767316161745581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32432517838511544107830387 48648776757767316161745581)
    ·
      refine ⟨18243291284162743560654593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48648776757767316161745581 18243291284162743560654593)
      ·
        refine ⟨13682468463122057670490945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18243291284162743560654593 13682468463122057670490945)
        ·
          refine ⟨10261851347341543252868209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13682468463122057670490945 10261851347341543252868209)
          ·
            refine ⟨7696388510506157439651157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10261851347341543252868209 7696388510506157439651157)
            ·
              refine ⟨11274006607186754061989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 7696388510506157439651157 11274006607186754061989)
              ·
                rfl

theorem cell23_1778440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 11].length) (baseStart_1778440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1778440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1778440 prefixEnd_1778440 := by exact prefixLift 1778440
  have htrace : WordTrace (prefixWord ++ tailWord_1778440) baseStart_1778440 baseEnd_1778440 := by
    simpa [prefixWord, tailWord_1778440, baseEnd_1778440] using wordTrace_append hprefix tailTrace_1778440
  have hstable : (prefixWord ++ tailWord_1778440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778440).length < 2 ^ (prefixWord ++ tailWord_1778440).sum := by decide
  have hdescent : baseEnd_1778440 < baseStart_1778440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778467 : List Nat := [1, 1, 1, 4, 2, 1, 1, 5, 1, 3, 3]
def baseStart_1778467 : Nat := 118140960795 + 1778467 * 2 ^ 59
def prefixEnd_1778467 : Nat := 4983230072969 + 3 ^ 40 * 1778467 * 2
def baseEnd_1778467 : Nat := 913208399159798473383485

theorem tailTrace_1778467 : CollatzResearch.WordTrace tailWord_1778467 prefixEnd_1778467 913208399159798473383485 := by
  unfold tailWord_1778467
  simp only [CollatzResearch.WordTrace]
  refine ⟨64866020447925271826893655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43244013631950181217929103 64866020447925271826893655)
  ·
    refine ⟨97299030671887907740340483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64866020447925271826893655 97299030671887907740340483)
    ·
      refine ⟨145948546007831861610510725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97299030671887907740340483 145948546007831861610510725)
      ·
        refine ⟨27365352376468474051970761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145948546007831861610510725 27365352376468474051970761)
        ·
          refine ⟨20524014282351355538978071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27365352376468474051970761 20524014282351355538978071)
          ·
            refine ⟨30786021423527033308467107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20524014282351355538978071 30786021423527033308467107)
            ·
              refine ⟨46179032135290549962700661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30786021423527033308467107 46179032135290549962700661)
              ·
                refine ⟨4329284262683489059003187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46179032135290549962700661 4329284262683489059003187)
                ·
                  refine ⟨6493926394025233588504781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4329284262683489059003187 6493926394025233588504781)
                  ·
                    refine ⟨2435222397759462595689293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6493926394025233588504781 2435222397759462595689293)
                    ·
                      refine ⟨913208399159798473383485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2435222397759462595689293 913208399159798473383485)
                      ·
                        rfl

theorem cell23_1778467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5, 1, 3, 3].length) (baseStart_1778467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1778467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1778467 prefixEnd_1778467 := by exact prefixLift 1778467
  have htrace : WordTrace (prefixWord ++ tailWord_1778467) baseStart_1778467 baseEnd_1778467 := by
    simpa [prefixWord, tailWord_1778467, baseEnd_1778467] using wordTrace_append hprefix tailTrace_1778467
  have hstable : (prefixWord ++ tailWord_1778467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778467).length < 2 ^ (prefixWord ++ tailWord_1778467).sum := by decide
  have hdescent : baseEnd_1778467 < baseStart_1778467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778468 : List Nat := [2, 3, 1, 3, 4, 1, 1, 2, 1, 1, 4]
def baseStart_1778468 : Nat := 118140960795 + 1778468 * 2 ^ 59
def prefixEnd_1778468 : Nat := 4983230072969 + 3 ^ 40 * 1778468 * 2
def baseEnd_1778468 : Nat := 913208912640452969470981

theorem tailTrace_1778468 : CollatzResearch.WordTrace tailWord_1778468 prefixEnd_1778468 913208912640452969470981 := by
  unfold tailWord_1778468
  simp only [CollatzResearch.WordTrace]
  refine ⟨32433028460460824498840029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43244037947281099331786705 32433028460460824498840029)
  ·
    refine ⟨12162385672672809187065011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32433028460460824498840029 12162385672672809187065011)
    ·
      refine ⟨18243578509009213780597517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12162385672672809187065011 18243578509009213780597517)
      ·
        refine ⟨6841341940878455167724069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18243578509009213780597517 6841341940878455167724069)
        ·
          refine ⟨1282751613914710343948263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6841341940878455167724069 1282751613914710343948263)
          ·
            refine ⟨1924127420872065515922395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1282751613914710343948263 1924127420872065515922395)
            ·
              refine ⟨2886191131308098273883593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1924127420872065515922395 2886191131308098273883593)
              ·
                refine ⟨2164643348481073705412695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2886191131308098273883593 2164643348481073705412695)
                ·
                  refine ⟨3246965022721610558119043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2164643348481073705412695 3246965022721610558119043)
                  ·
                    refine ⟨4870447534082415837178565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3246965022721610558119043 4870447534082415837178565)
                    ·
                      refine ⟨913208912640452969470981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4870447534082415837178565 913208912640452969470981)
                      ·
                        rfl

theorem cell23_1778468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_1778468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1778468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1778468 prefixEnd_1778468 := by exact prefixLift 1778468
  have htrace : WordTrace (prefixWord ++ tailWord_1778468) baseStart_1778468 baseEnd_1778468 := by
    simpa [prefixWord, tailWord_1778468, baseEnd_1778468] using wordTrace_append hprefix tailTrace_1778468
  have hstable : (prefixWord ++ tailWord_1778468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778468).length < 2 ^ (prefixWord ++ tailWord_1778468).sum := by decide
  have hdescent : baseEnd_1778468 < baseStart_1778468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778480 : List Nat := [2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 5]
def baseStart_1778480 : Nat := 118140960795 + 1778480 * 2 ^ 59
def prefixEnd_1778480 : Nat := 4983230072969 + 3 ^ 40 * 1778480 * 2
def baseEnd_1778480 : Nat := 913215074408306922520925

theorem tailTrace_1778480 : CollatzResearch.WordTrace tailWord_1778480 prefixEnd_1778480 913215074408306922520925 := by
  unfold tailWord_1778480
  simp only [CollatzResearch.WordTrace]
  refine ⟨32433247298439087523558447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43244329731252116698077929 32433247298439087523558447)
  ·
    refine ⟨48649870947658631285337671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32433247298439087523558447 48649870947658631285337671)
    ·
      refine ⟨72974806421487946928006507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48649870947658631285337671 72974806421487946928006507)
      ·
        refine ⟨109462209632231920392009761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72974806421487946928006507 109462209632231920392009761)
        ·
          refine ⟨82096657224173940294007321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109462209632231920392009761 82096657224173940294007321)
          ·
            refine ⟨61572492918130455220505491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82096657224173940294007321 61572492918130455220505491)
            ·
              refine ⟨92358739377195682830758237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61572492918130455220505491 92358739377195682830758237)
              ·
                refine ⟨34634527266448381061534339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92358739377195682830758237 34634527266448381061534339)
                ·
                  refine ⟨51951790899672571592301509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34634527266448381061534339 51951790899672571592301509)
                  ·
                    refine ⟨9740960793688607173556533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51951790899672571592301509 9740960793688607173556533)
                    ·
                      refine ⟨913215074408306922520925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9740960793688607173556533 913215074408306922520925)
                      ·
                        rfl

theorem cell23_1778480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 5].length) (baseStart_1778480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1778480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1778480 prefixEnd_1778480 := by exact prefixLift 1778480
  have htrace : WordTrace (prefixWord ++ tailWord_1778480) baseStart_1778480 baseEnd_1778480 := by
    simpa [prefixWord, tailWord_1778480, baseEnd_1778480] using wordTrace_append hprefix tailTrace_1778480
  have hstable : (prefixWord ++ tailWord_1778480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778480).length < 2 ^ (prefixWord ++ tailWord_1778480).sum := by decide
  have hdescent : baseEnd_1778480 < baseStart_1778480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778517 : List Nat := [1, 3, 2, 2, 2, 1, 3, 1, 2, 6]
def baseStart_1778517 : Nat := 118140960795 + 1778517 * 2 ^ 59
def prefixEnd_1778517 : Nat := 4983230072969 + 3 ^ 40 * 1778517 * 2
def baseEnd_1778517 : Nat := 304411357730841092586085

theorem tailTrace_1778517 : CollatzResearch.WordTrace tailWord_1778517 prefixEnd_1778517 304411357730841092586085 := by
  unfold tailWord_1778517
  simp only [CollatzResearch.WordTrace]
  refine ⟨64867844097744130366213805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43245229398496086910809203 64867844097744130366213805)
  ·
    refine ⟨24325441536654048887330177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64867844097744130366213805 24325441536654048887330177)
    ·
      refine ⟨18244081152490536665497633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24325441536654048887330177 18244081152490536665497633)
      ·
        refine ⟨13683060864367902499123225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18244081152490536665497633 13683060864367902499123225)
        ·
          refine ⟨10262295648275926874342419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13683060864367902499123225 10262295648275926874342419)
          ·
            refine ⟨15393443472413890311513629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10262295648275926874342419 15393443472413890311513629)
            ·
              refine ⟨5772541302155208866817611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15393443472413890311513629 5772541302155208866817611)
              ·
                refine ⟨8658811953232813300226417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5772541302155208866817611 8658811953232813300226417)
                ·
                  refine ⟨6494108964924609975169813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8658811953232813300226417 6494108964924609975169813)
                  ·
                    refine ⟨304411357730841092586085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6494108964924609975169813 304411357730841092586085)
                    ·
                      rfl

theorem cell23_1778517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 2, 6].length) (baseStart_1778517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1778517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1778517 prefixEnd_1778517 := by exact prefixLift 1778517
  have htrace : WordTrace (prefixWord ++ tailWord_1778517) baseStart_1778517 baseEnd_1778517 := by
    simpa [prefixWord, tailWord_1778517, baseEnd_1778517] using wordTrace_append hprefix tailTrace_1778517
  have hstable : (prefixWord ++ tailWord_1778517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778517).length < 2 ^ (prefixWord ++ tailWord_1778517).sum := by decide
  have hdescent : baseEnd_1778517 < baseStart_1778517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778527 : List Nat := [1, 1, 2, 3, 1, 3, 1, 2, 2, 4, 3]
def baseStart_1778527 : Nat := 118140960795 + 1778527 * 2 ^ 59
def prefixEnd_1778527 : Nat := 4983230072969 + 3 ^ 40 * 1778527 * 2
def baseEnd_1778527 : Nat := 913239207999068238633209

theorem tailTrace_1778527 : CollatzResearch.WordTrace tailWord_1778527 prefixEnd_1778527 913239207999068238633209 := by
  unfold tailWord_1778527
  simp only [CollatzResearch.WordTrace]
  refine ⟨64868208827707902074077835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43245472551805268049385223 64868208827707902074077835)
  ·
    refine ⟨97302313241561853111116753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64868208827707902074077835 97302313241561853111116753)
    ·
      refine ⟨72976734931171389833337565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97302313241561853111116753 72976734931171389833337565)
      ·
        refine ⟨27366275599189271187501587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72976734931171389833337565 27366275599189271187501587)
        ·
          refine ⟨41049413398783906781252381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27366275599189271187501587 41049413398783906781252381)
          ·
            refine ⟨15393530024543965042969643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41049413398783906781252381 15393530024543965042969643)
            ·
              refine ⟨23090295036815947564454465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15393530024543965042969643 23090295036815947564454465)
              ·
                refine ⟨17317721277611960673340849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23090295036815947564454465 17317721277611960673340849)
                ·
                  refine ⟨12988290958208970505005637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17317721277611960673340849 12988290958208970505005637)
                  ·
                    refine ⟨2435304554664181969688557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12988290958208970505005637 2435304554664181969688557)
                    ·
                      refine ⟨913239207999068238633209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2435304554664181969688557 913239207999068238633209)
                      ·
                        rfl

theorem cell23_1778527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 4, 3].length) (baseStart_1778527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1778527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1778527 prefixEnd_1778527 := by exact prefixLift 1778527
  have htrace : WordTrace (prefixWord ++ tailWord_1778527) baseStart_1778527 baseEnd_1778527 := by
    simpa [prefixWord, tailWord_1778527, baseEnd_1778527] using wordTrace_append hprefix tailTrace_1778527
  have hstable : (prefixWord ++ tailWord_1778527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778527).length < 2 ^ (prefixWord ++ tailWord_1778527).sum := by decide
  have hdescent : baseEnd_1778527 < baseStart_1778527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778541 : List Nat := [1, 5, 1, 1, 1, 1, 1, 4, 4, 2, 2]
def baseStart_1778541 : Nat := 118140960795 + 1778541 * 2 ^ 59
def prefixEnd_1778541 : Nat := 4983230072969 + 3 ^ 40 * 1778541 * 2
def baseEnd_1778541 : Nat := 913246396728231183858145

theorem tailTrace_1778541 : CollatzResearch.WordTrace tailWord_1778541 prefixEnd_1778541 913246396728231183858145 := by
  unfold tailWord_1778541
  simp only [CollatzResearch.WordTrace]
  refine ⟨64868719449657182465087477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43245812966438121643391651 64868719449657182465087477)
  ·
    refine ⟨6081442448405360856101951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64868719449657182465087477 6081442448405360856101951)
    ·
      refine ⟨9122163672608041284152927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6081442448405360856101951 9122163672608041284152927)
      ·
        refine ⟨13683245508912061926229391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9122163672608041284152927 13683245508912061926229391)
        ·
          refine ⟨20524868263368092889344087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13683245508912061926229391 20524868263368092889344087)
          ·
            refine ⟨30787302395052139334016131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20524868263368092889344087 30787302395052139334016131)
            ·
              refine ⟨46180953592578209001024197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30787302395052139334016131 46180953592578209001024197)
              ·
                refine ⟨8658928798608414187692037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46180953592578209001024197 8658928798608414187692037)
                ·
                  refine ⟨1623549149739077660192257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8658928798608414187692037 1623549149739077660192257)
                  ·
                    refine ⟨1217661862304308245144193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1623549149739077660192257 1217661862304308245144193)
                    ·
                      refine ⟨913246396728231183858145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1217661862304308245144193 913246396728231183858145)
                      ·
                        rfl

theorem cell23_1778541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 4, 2, 2].length) (baseStart_1778541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1778541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1778541 prefixEnd_1778541 := by exact prefixLift 1778541
  have htrace : WordTrace (prefixWord ++ tailWord_1778541) baseStart_1778541 baseEnd_1778541 := by
    simpa [prefixWord, tailWord_1778541, baseEnd_1778541] using wordTrace_append hprefix tailTrace_1778541
  have hstable : (prefixWord ++ tailWord_1778541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778541).length < 2 ^ (prefixWord ++ tailWord_1778541).sum := by decide
  have hdescent : baseEnd_1778541 < baseStart_1778541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778594 : List Nat := [3, 3, 1, 2, 2, 1, 2, 1, 1, 7]
def baseStart_1778594 : Nat := 118140960795 + 1778594 * 2 ^ 59
def prefixEnd_1778594 : Nat := 4983230072969 + 3 ^ 40 * 1778594 * 2
def baseEnd_1778594 : Nat := 304424537067639825498467

theorem tailTrace_1778594 : CollatzResearch.WordTrace tailWord_1778594 prefixEnd_1778594 304424537067639825498467 := by
  unfold tailWord_1778594
  simp only [CollatzResearch.WordTrace]
  refine ⟨16217663129616293129191709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43247101678976781677844557 16217663129616293129191709)
  ·
    refine ⟨6081623673606109923446891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16217663129616293129191709 6081623673606109923446891)
    ·
      refine ⟨9122435510409164885170337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6081623673606109923446891 9122435510409164885170337)
      ·
        refine ⟨6841826632806873663877753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9122435510409164885170337 6841826632806873663877753)
        ·
          refine ⟨5131369974605155247908315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6841826632806873663877753 5131369974605155247908315)
          ·
            refine ⟨7697054961907732871862473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5131369974605155247908315 7697054961907732871862473)
            ·
              refine ⟨5772791221430799653896855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7697054961907732871862473 5772791221430799653896855)
              ·
                refine ⟨8659186832146199480845283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5772791221430799653896855 8659186832146199480845283)
                ·
                  refine ⟨12988780248219299221267925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8659186832146199480845283 12988780248219299221267925)
                  ·
                    refine ⟨304424537067639825498467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12988780248219299221267925 304424537067639825498467)
                    ·
                      rfl

theorem cell23_1778594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_1778594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1778594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1778594 prefixEnd_1778594 := by exact prefixLift 1778594
  have htrace : WordTrace (prefixWord ++ tailWord_1778594) baseStart_1778594 baseEnd_1778594 := by
    simpa [prefixWord, tailWord_1778594, baseEnd_1778594] using wordTrace_append hprefix tailTrace_1778594
  have hstable : (prefixWord ++ tailWord_1778594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778594).length < 2 ^ (prefixWord ++ tailWord_1778594).sum := by decide
  have hdescent : baseEnd_1778594 < baseStart_1778594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778634 : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 6, 2, 3]
def baseStart_1778634 : Nat := 118140960795 + 1778634 * 2 ^ 59
def prefixEnd_1778634 : Nat := 4983230072969 + 3 ^ 40 * 1778634 * 2
def baseEnd_1778634 : Nat := 913294150429099319995217

theorem tailTrace_1778634 : CollatzResearch.WordTrace tailWord_1778634 prefixEnd_1778634 913294150429099319995217 := by
  unfold tailWord_1778634
  simp only [CollatzResearch.WordTrace]
  refine ⟨16218027859580064837055739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43248074292213506232148637 16218027859580064837055739)
  ·
    refine ⟨24327041789370097255583609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16218027859580064837055739 24327041789370097255583609)
    ·
      refine ⟨18245281342027572941687707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24327041789370097255583609 18245281342027572941687707)
      ·
        refine ⟨27367922013041359412531561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18245281342027572941687707 27367922013041359412531561)
        ·
          refine ⟨20525941509781019559398671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27367922013041359412531561 20525941509781019559398671)
          ·
            refine ⟨30788912264671529339098007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20525941509781019559398671 30788912264671529339098007)
            ·
              refine ⟨46183368397007294008647011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30788912264671529339098007 46183368397007294008647011)
              ·
                refine ⟨69275052595510941012970517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46183368397007294008647011 69275052595510941012970517)
                ·
                  refine ⟨3247268090414575359982993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 69275052595510941012970517 3247268090414575359982993)
                  ·
                    refine ⟨2435451067810931519987245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3247268090414575359982993 2435451067810931519987245)
                    ·
                      refine ⟨913294150429099319995217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2435451067810931519987245 913294150429099319995217)
                      ·
                        rfl

theorem cell23_1778634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 6, 2, 3].length) (baseStart_1778634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1778634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1778634 prefixEnd_1778634 := by exact prefixLift 1778634
  have htrace : WordTrace (prefixWord ++ tailWord_1778634) baseStart_1778634 baseEnd_1778634 := by
    simpa [prefixWord, tailWord_1778634, baseEnd_1778634] using wordTrace_append hprefix tailTrace_1778634
  have hstable : (prefixWord ++ tailWord_1778634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778634).length < 2 ^ (prefixWord ++ tailWord_1778634).sum := by decide
  have hdescent : baseEnd_1778634 < baseStart_1778634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778657 : List Nat := [1, 2, 3, 1, 2, 1, 1, 2, 1, 1, 8]
def baseStart_1778657 : Nat := 118140960795 + 1778657 * 2 ^ 59
def prefixEnd_1778657 : Nat := 4983230072969 + 3 ^ 40 * 1778657 * 2
def baseEnd_1778657 : Nat := 913305960484152730007611

theorem tailTrace_1778657 : CollatzResearch.WordTrace tailWord_1778657 prefixEnd_1778657 913305960484152730007611 := by
  unfold tailWord_1778657
  simp only [CollatzResearch.WordTrace]
  refine ⟨64872950317236934276310225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43248633544824622850873483 64872950317236934276310225)
  ·
    refine ⟨48654712737927700707232669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64872950317236934276310225 48654712737927700707232669)
    ·
      refine ⟨18245517276722887765212251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48654712737927700707232669 18245517276722887765212251)
      ·
        refine ⟨27368275915084331647818377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18245517276722887765212251 27368275915084331647818377)
        ·
          refine ⟨20526206936313248735863783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27368275915084331647818377 20526206936313248735863783)
          ·
            refine ⟨30789310404469873103795675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20526206936313248735863783 30789310404469873103795675)
            ·
              refine ⟨46183965606704809655693513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30789310404469873103795675 46183965606704809655693513)
              ·
                refine ⟨34637974205028607241770135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46183965606704809655693513 34637974205028607241770135)
                ·
                  refine ⟨51956961307542910862655203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34637974205028607241770135 51956961307542910862655203)
                  ·
                    refine ⟨77935441961314366293982805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51956961307542910862655203 77935441961314366293982805)
                    ·
                      refine ⟨913305960484152730007611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 77935441961314366293982805 913305960484152730007611)
                      ·
                        rfl

theorem cell23_1778657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_1778657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1778657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1778657 prefixEnd_1778657 := by exact prefixLift 1778657
  have htrace : WordTrace (prefixWord ++ tailWord_1778657) baseStart_1778657 baseEnd_1778657 := by
    simpa [prefixWord, tailWord_1778657, baseEnd_1778657] using wordTrace_append hprefix tailTrace_1778657
  have hstable : (prefixWord ++ tailWord_1778657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778657).length < 2 ^ (prefixWord ++ tailWord_1778657).sum := by decide
  have hdescent : baseEnd_1778657 < baseStart_1778657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778681 : List Nat := [1, 2, 1, 3, 1, 3, 2, 3, 3, 1, 3]
def baseStart_1778681 : Nat := 118140960795 + 1778681 * 2 ^ 59
def prefixEnd_1778681 : Nat := 4983230072969 + 3 ^ 40 * 1778681 * 2
def baseEnd_1778681 : Nat := 913318284019860636107501

theorem tailTrace_1778681 : CollatzResearch.WordTrace tailWord_1778681 prefixEnd_1778681 913318284019860636107501 := by
  unfold tailWord_1778681
  simp only [CollatzResearch.WordTrace]
  refine ⟨64873825669149986375183897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43249217112766657583455931 64873825669149986375183897)
  ·
    refine ⟨48655369251862489781387923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64873825669149986375183897 48655369251862489781387923)
    ·
      refine ⟨72983053877793734672081885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48655369251862489781387923 72983053877793734672081885)
      ·
        refine ⟨27368645204172650502030707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72983053877793734672081885 27368645204172650502030707)
        ·
          refine ⟨41052967806258975753046061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27368645204172650502030707 41052967806258975753046061)
          ·
            refine ⟨15394862927347115907392273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41052967806258975753046061 15394862927347115907392273)
            ·
              refine ⟨11546147195510336930544205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15394862927347115907392273 11546147195510336930544205)
              ·
                refine ⟨4329805198316376348954077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11546147195510336930544205 4329805198316376348954077)
                ·
                  refine ⟨1623676949368641130857779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4329805198316376348954077 1623676949368641130857779)
                  ·
                    refine ⟨2435515424052961696286669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1623676949368641130857779 2435515424052961696286669)
                    ·
                      refine ⟨913318284019860636107501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2435515424052961696286669 913318284019860636107501)
                      ·
                        rfl

theorem cell23_1778681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3, 3, 1, 3].length) (baseStart_1778681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1778681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1778681 prefixEnd_1778681 := by exact prefixLift 1778681
  have htrace : WordTrace (prefixWord ++ tailWord_1778681) baseStart_1778681 baseEnd_1778681 := by
    simpa [prefixWord, tailWord_1778681, baseEnd_1778681] using wordTrace_append hprefix tailTrace_1778681
  have hstable : (prefixWord ++ tailWord_1778681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778681).length < 2 ^ (prefixWord ++ tailWord_1778681).sum := by decide
  have hdescent : baseEnd_1778681 < baseStart_1778681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778684 : List Nat := [2, 2, 2, 1, 2, 3, 1, 2, 3, 5]
def baseStart_1778684 : Nat := 118140960795 + 1778684 * 2 ^ 59
def prefixEnd_1778684 : Nat := 4983230072969 + 3 ^ 40 * 1778684 * 2
def baseEnd_1778684 : Nat := 304439941487274708123329

theorem tailTrace_1778684 : CollatzResearch.WordTrace tailWord_1778684 prefixEnd_1778684 304439941487274708123329 := by
  unfold tailWord_1778684
  simp only [CollatzResearch.WordTrace]
  refine ⟨32436967544069558943771553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43249290058759411925028737 32436967544069558943771553)
  ·
    refine ⟨24327725658052169207828665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32436967544069558943771553 24327725658052169207828665)
    ·
      refine ⟨18245794243539126905871499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24327725658052169207828665 18245794243539126905871499)
      ·
        refine ⟨27368691365308690358807249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18245794243539126905871499 27368691365308690358807249)
        ·
          refine ⟨20526518523981517769105437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27368691365308690358807249 20526518523981517769105437)
          ·
            refine ⟨7697444446493069163414539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20526518523981517769105437 7697444446493069163414539)
            ·
              refine ⟨11546166669739603745121809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7697444446493069163414539 11546166669739603745121809)
              ·
                refine ⟨8659625002304702808841357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11546166669739603745121809 8659625002304702808841357)
                ·
                  refine ⟨3247359375864263553315509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8659625002304702808841357 3247359375864263553315509)
                  ·
                    refine ⟨304439941487274708123329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3247359375864263553315509 304439941487274708123329)
                    ·
                      rfl

theorem cell23_1778684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 3, 5].length) (baseStart_1778684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1778684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1778684 prefixEnd_1778684 := by exact prefixLift 1778684
  have htrace : WordTrace (prefixWord ++ tailWord_1778684) baseStart_1778684 baseEnd_1778684 := by
    simpa [prefixWord, tailWord_1778684, baseEnd_1778684] using wordTrace_append hprefix tailTrace_1778684
  have hstable : (prefixWord ++ tailWord_1778684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778684).length < 2 ^ (prefixWord ++ tailWord_1778684).sum := by decide
  have hdescent : baseEnd_1778684 < baseStart_1778684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778698 : List Nat := [3, 1, 2, 2, 3, 2, 1, 2, 3, 1, 3]
def baseStart_1778698 : Nat := 118140960795 + 1778698 * 2 ^ 59
def prefixEnd_1778698 : Nat := 4983230072969 + 3 ^ 40 * 1778698 * 2
def baseEnd_1778698 : Nat := 913327013190987069594923

theorem tailTrace_1778698 : CollatzResearch.WordTrace tailWord_1778698 prefixEnd_1778698 913327013190987069594923 := by
  unfold tailWord_1778698
  simp only [CollatzResearch.WordTrace]
  refine ⟨16218611427522099569638187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43249630473392265519035165 16218611427522099569638187)
  ·
    refine ⟨24327917141283149354457281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16218611427522099569638187 24327917141283149354457281)
    ·
      refine ⟨18245937855962362015842961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24327917141283149354457281 18245937855962362015842961)
      ·
        refine ⟨13684453391971771511882221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18245937855962362015842961 13684453391971771511882221)
        ·
          refine ⟨5131670021989414316955833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13684453391971771511882221 5131670021989414316955833)
          ·
            refine ⟨3848752516492060737716875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5131670021989414316955833 3848752516492060737716875)
            ·
              refine ⟨5773128774738091106575313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3848752516492060737716875 5773128774738091106575313)
              ·
                refine ⟨4329846581053568329931485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5773128774738091106575313 4329846581053568329931485)
                ·
                  refine ⟨1623692467895088123724307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4329846581053568329931485 1623692467895088123724307)
                  ·
                    refine ⟨2435538701842632185586461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1623692467895088123724307 2435538701842632185586461)
                    ·
                      refine ⟨913327013190987069594923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2435538701842632185586461 913327013190987069594923)
                      ·
                        rfl

theorem cell23_1778698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 2, 3, 1, 3].length) (baseStart_1778698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1778698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1778698 prefixEnd_1778698 := by exact prefixLift 1778698
  have htrace : WordTrace (prefixWord ++ tailWord_1778698) baseStart_1778698 baseEnd_1778698 := by
    simpa [prefixWord, tailWord_1778698, baseEnd_1778698] using wordTrace_append hprefix tailTrace_1778698
  have hstable : (prefixWord ++ tailWord_1778698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778698).length < 2 ^ (prefixWord ++ tailWord_1778698).sum := by decide
  have hdescent : baseEnd_1778698 < baseStart_1778698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778714 : List Nat := [3, 1, 1, 3, 1, 2, 1, 4, 1, 6]
def baseStart_1778714 : Nat := 118140960795 + 1778714 * 2 ^ 59
def prefixEnd_1778714 : Nat := 4983230072969 + 3 ^ 40 * 1778714 * 2
def baseEnd_1778714 : Nat := 304445076293819668998283

theorem tailTrace_1778714 : CollatzResearch.WordTrace tailWord_1778714 prefixEnd_1778714 304445076293819668998283 := by
  unfold tailWord_1778714
  simp only [CollatzResearch.WordTrace]
  refine ⟨16218757319507608252783799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43250019518686955340756797 16218757319507608252783799)
  ·
    refine ⟨24328135979261412379175699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16218757319507608252783799 24328135979261412379175699)
    ·
      refine ⟨36492203968892118568763549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24328135979261412379175699 36492203968892118568763549)
      ·
        refine ⟨13684576488334544463286331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36492203968892118568763549 13684576488334544463286331)
        ·
          refine ⟨20526864732501816694929497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13684576488334544463286331 20526864732501816694929497)
          ·
            refine ⟨15395148549376362521197123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20526864732501816694929497 15395148549376362521197123)
            ·
              refine ⟨23092722824064543781795685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15395148549376362521197123 23092722824064543781795685)
              ·
                refine ⟨4329885529512101959086691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23092722824064543781795685 4329885529512101959086691)
                ·
                  refine ⟨6494828294268152938630037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4329885529512101959086691 6494828294268152938630037)
                  ·
                    refine ⟨304445076293819668998283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6494828294268152938630037 304445076293819668998283)
                    ·
                      rfl

theorem cell23_1778714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4, 1, 6].length) (baseStart_1778714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1778714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1778714 prefixEnd_1778714 := by exact prefixLift 1778714
  have htrace : WordTrace (prefixWord ++ tailWord_1778714) baseStart_1778714 baseEnd_1778714 := by
    simpa [prefixWord, tailWord_1778714, baseEnd_1778714] using wordTrace_append hprefix tailTrace_1778714
  have hstable : (prefixWord ++ tailWord_1778714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778714).length < 2 ^ (prefixWord ++ tailWord_1778714).sum := by decide
  have hdescent : baseEnd_1778714 < baseStart_1778714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778771 : List Nat := [1, 1, 1, 2, 1, 1, 2, 6, 4, 1, 3]
def baseStart_1778771 : Nat := 118140960795 + 1778771 * 2 ^ 59
def prefixEnd_1778771 : Nat := 4983230072969 + 3 ^ 40 * 1778771 * 2
def baseEnd_1778771 : Nat := 913364497278765283982087

theorem tailTrace_1778771 : CollatzResearch.WordTrace tailWord_1778771 prefixEnd_1778771 913364497278765283982087 := by
  unfold tailWord_1778771
  simp only [CollatzResearch.WordTrace]
  refine ⟨64877108238823931745960167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43251405492549287830640111 64877108238823931745960167)
  ·
    refine ⟨97315662358235897618940251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64877108238823931745960167 97315662358235897618940251)
    ·
      refine ⟨145973493537353846428410377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97315662358235897618940251 145973493537353846428410377)
      ·
        refine ⟨109480120153015384821307783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145973493537353846428410377 109480120153015384821307783)
        ·
          refine ⟨164220180229523077231961675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109480120153015384821307783 164220180229523077231961675)
          ·
            refine ⟨246330270344284615847942513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164220180229523077231961675 246330270344284615847942513)
            ·
              refine ⟨184747702758213461885956885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246330270344284615847942513 184747702758213461885956885)
              ·
                refine ⟨8660048566791256025904229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 184747702758213461885956885 8660048566791256025904229)
                ·
                  refine ⟨1623759106273360504857043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8660048566791256025904229 1623759106273360504857043)
                  ·
                    refine ⟨2435638659410040757285565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1623759106273360504857043 2435638659410040757285565)
                    ·
                      refine ⟨913364497278765283982087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2435638659410040757285565 913364497278765283982087)
                      ·
                        rfl

theorem cell23_1778771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 4, 1, 3].length) (baseStart_1778771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1778771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1778771 prefixEnd_1778771 := by exact prefixLift 1778771
  have htrace : WordTrace (prefixWord ++ tailWord_1778771) baseStart_1778771 baseEnd_1778771 := by
    simpa [prefixWord, tailWord_1778771, baseEnd_1778771] using wordTrace_append hprefix tailTrace_1778771
  have hstable : (prefixWord ++ tailWord_1778771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778771).length < 2 ^ (prefixWord ++ tailWord_1778771).sum := by decide
  have hdescent : baseEnd_1778771 < baseStart_1778771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778772 : List Nat := [2, 4, 1, 1, 1, 1, 5, 3, 1, 2, 2]
def baseStart_1778772 : Nat := 118140960795 + 1778772 * 2 ^ 59
def prefixEnd_1778772 : Nat := 4983230072969 + 3 ^ 40 * 1778772 * 2
def baseEnd_1778772 : Nat := 913365010759419780069583

theorem tailTrace_1778772 : CollatzResearch.WordTrace tailWord_1778772 prefixEnd_1778772 913365010759419780069583 := by
  unfold tailWord_1778772
  simp only [CollatzResearch.WordTrace]
  refine ⟨32438572355910154458373285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43251429807880205944497713 32438572355910154458373285)
  ·
    refine ⟨6082232316733153960944991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32438572355910154458373285 6082232316733153960944991)
    ·
      refine ⟨9123348475099730941417487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6082232316733153960944991 9123348475099730941417487)
      ·
        refine ⟨13685022712649596412126231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9123348475099730941417487 13685022712649596412126231)
        ·
          refine ⟨20527534068974394618189347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13685022712649596412126231 20527534068974394618189347)
          ·
            refine ⟨30791301103461591927284021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20527534068974394618189347 30791301103461591927284021)
            ·
              refine ⟨2886684478449524243182877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30791301103461591927284021 2886684478449524243182877)
              ·
                refine ⟨1082506679418571591193579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2886684478449524243182877 1082506679418571591193579)
                ·
                  refine ⟨1623760019127857386790369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1082506679418571591193579 1623760019127857386790369)
                  ·
                    refine ⟨1217820014345893040092777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1623760019127857386790369 1217820014345893040092777)
                    ·
                      refine ⟨913365010759419780069583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1217820014345893040092777 913365010759419780069583)
                      ·
                        rfl

theorem cell23_1778772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 3, 1, 2, 2].length) (baseStart_1778772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1778772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1778772 prefixEnd_1778772 := by exact prefixLift 1778772
  have htrace : WordTrace (prefixWord ++ tailWord_1778772) baseStart_1778772 baseEnd_1778772 := by
    simpa [prefixWord, tailWord_1778772, baseEnd_1778772] using wordTrace_append hprefix tailTrace_1778772
  have hstable : (prefixWord ++ tailWord_1778772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778772).length < 2 ^ (prefixWord ++ tailWord_1778772).sum := by decide
  have hdescent : baseEnd_1778772 < baseStart_1778772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778784 : List Nat := [2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 5]
def baseStart_1778784 : Nat := 118140960795 + 1778784 * 2 ^ 59
def prefixEnd_1778784 : Nat := 4983230072969 + 3 ^ 40 * 1778784 * 2
def baseEnd_1778784 : Nat := 913371172527273733119527

theorem tailTrace_1778784 : CollatzResearch.WordTrace tailWord_1778784 prefixEnd_1778784 913371172527273733119527 := by
  unfold tailWord_1778784
  simp only [CollatzResearch.WordTrace]
  refine ⟨32438791193888417483091703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43251721591851223310788937 32438791193888417483091703)
  ·
    refine ⟨48658186790832626224637555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32438791193888417483091703 48658186790832626224637555)
    ·
      refine ⟨72987280186248939336956333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48658186790832626224637555 72987280186248939336956333)
      ·
        refine ⟨27370230069843352251358625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72987280186248939336956333 27370230069843352251358625)
        ·
          refine ⟨20527672552382514188518969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27370230069843352251358625 20527672552382514188518969)
          ·
            refine ⟨15395754414286885641389227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20527672552382514188518969 15395754414286885641389227)
            ·
              refine ⟨23093631621430328462083841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15395754414286885641389227 23093631621430328462083841)
              ·
                refine ⟨17320223716072746346562881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23093631621430328462083841 17320223716072746346562881)
                ·
                  refine ⟨12990167787054559759922161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17320223716072746346562881 12990167787054559759922161)
                  ·
                    refine ⟨9742625840290919819941621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12990167787054559759922161 9742625840290919819941621)
                    ·
                      refine ⟨913371172527273733119527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9742625840290919819941621 913371172527273733119527)
                      ·
                        rfl

theorem cell23_1778784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_1778784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1778784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1778784 prefixEnd_1778784 := by exact prefixLift 1778784
  have htrace : WordTrace (prefixWord ++ tailWord_1778784) baseStart_1778784 baseEnd_1778784 := by
    simpa [prefixWord, tailWord_1778784, baseEnd_1778784] using wordTrace_append hprefix tailTrace_1778784
  have hstable : (prefixWord ++ tailWord_1778784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778784).length < 2 ^ (prefixWord ++ tailWord_1778784).sum := by decide
  have hdescent : baseEnd_1778784 < baseStart_1778784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778788 : List Nat := [2, 3, 1, 1, 2, 1, 1, 6, 2, 1, 3]
def baseStart_1778788 : Nat := 118140960795 + 1778788 * 2 ^ 59
def prefixEnd_1778788 : Nat := 4983230072969 + 3 ^ 40 * 1778788 * 2
def baseEnd_1778788 : Nat := 913373226449891717469509

theorem tailTrace_1778788 : CollatzResearch.WordTrace tailWord_1778788 prefixEnd_1778788 913373226449891717469509 := by
  unfold tailWord_1778788
  simp only [CollatzResearch.WordTrace]
  refine ⟨32438864139881171824664509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43251818853174895766219345 32438864139881171824664509)
  ·
    refine ⟨12164574052455439434249191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32438864139881171824664509 12164574052455439434249191)
    ·
      refine ⟨18246861078683159151373787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12164574052455439434249191 18246861078683159151373787)
      ·
        refine ⟨27370291618024738727060681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18246861078683159151373787 27370291618024738727060681)
        ·
          refine ⟨20527718713518554045295511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27370291618024738727060681 20527718713518554045295511)
          ·
            refine ⟨30791578070277831067943267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20527718713518554045295511 30791578070277831067943267)
            ·
              refine ⟨46187367105416746601914901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30791578070277831067943267 46187367105416746601914901)
              ·
                refine ⟨2165032833066409996964761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46187367105416746601914901 2165032833066409996964761)
                ·
                  refine ⟨1623774624799807497723571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2165032833066409996964761 1623774624799807497723571)
                  ·
                    refine ⟨2435661937199711246585357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1623774624799807497723571 2435661937199711246585357)
                    ·
                      refine ⟨913373226449891717469509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2435661937199711246585357 913373226449891717469509)
                      ·
                        rfl

theorem cell23_1778788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 6, 2, 1, 3].length) (baseStart_1778788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1778788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1778788 prefixEnd_1778788 := by exact prefixLift 1778788
  have htrace : WordTrace (prefixWord ++ tailWord_1778788) baseStart_1778788 baseEnd_1778788 := by
    simpa [prefixWord, tailWord_1778788, baseEnd_1778788] using wordTrace_append hprefix tailTrace_1778788
  have hstable : (prefixWord ++ tailWord_1778788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778788).length < 2 ^ (prefixWord ++ tailWord_1778788).sum := by decide
  have hdescent : baseEnd_1778788 < baseStart_1778788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778811 : List Nat := [1, 1, 1, 1, 1, 4, 1, 2, 5, 4, 2]
def baseStart_1778811 : Nat := 118140960795 + 1778811 * 2 ^ 59
def prefixEnd_1778811 : Nat := 4983230072969 + 3 ^ 40 * 1778811 * 2
def baseEnd_1778811 : Nat := 913385036504945127481903

theorem tailTrace_1778811 : CollatzResearch.WordTrace tailWord_1778811 prefixEnd_1778811 913385036504945127481903 := by
  unfold tailWord_1778811
  simp only [CollatzResearch.WordTrace]
  refine ⟨64878567158679018577416287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43252378105786012384944191 64878567158679018577416287)
  ·
    refine ⟨97317850738018527866124431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64878567158679018577416287 97317850738018527866124431)
    ·
      refine ⟨145976776107027791799186647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97317850738018527866124431 145976776107027791799186647)
      ·
        refine ⟨218965164160541687698779971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145976776107027791799186647 218965164160541687698779971)
        ·
          refine ⟨328447746240812531548169957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218965164160541687698779971 328447746240812531548169957)
          ·
            refine ⟨61583952420152349665281867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 328447746240812531548169957 61583952420152349665281867)
            ·
              refine ⟨92375928630228524497922801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61583952420152349665281867 92375928630228524497922801)
              ·
                refine ⟨69281946472671393373442101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92375928630228524497922801 69281946472671393373442101)
                ·
                  refine ⟨6495182481812943128760197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69281946472671393373442101 6495182481812943128760197)
                  ·
                    refine ⟨1217846715339926836642537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6495182481812943128760197 1217846715339926836642537)
                    ·
                      refine ⟨913385036504945127481903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1217846715339926836642537 913385036504945127481903)
                      ·
                        rfl

theorem cell23_1778811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5, 4, 2].length) (baseStart_1778811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1778811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1778811 prefixEnd_1778811 := by exact prefixLift 1778811
  have htrace : WordTrace (prefixWord ++ tailWord_1778811) baseStart_1778811 baseEnd_1778811 := by
    simpa [prefixWord, tailWord_1778811, baseEnd_1778811] using wordTrace_append hprefix tailTrace_1778811
  have hstable : (prefixWord ++ tailWord_1778811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778811).length < 2 ^ (prefixWord ++ tailWord_1778811).sum := by decide
  have hdescent : baseEnd_1778811 < baseStart_1778811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778828 : List Nat := [2, 2, 1, 2, 1, 1, 1, 3, 6, 2, 2]
def baseStart_1778828 : Nat := 118140960795 + 1778828 * 2 ^ 59
def prefixEnd_1778828 : Nat := 4983230072969 + 3 ^ 40 * 1778828 * 2
def baseEnd_1778828 : Nat := 913393765676071560969325

theorem tailTrace_1778828 : CollatzResearch.WordTrace tailWord_1778828 prefixEnd_1778828 913393765676071560969325 := by
  unfold tailWord_1778828
  simp only [CollatzResearch.WordTrace]
  refine ⟨32439593599808715240392569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43252791466411620320523425 32439593599808715240392569)
  ·
    refine ⟨24329695199856536430294427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32439593599808715240392569 24329695199856536430294427)
    ·
      refine ⟨36494542799784804645441641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24329695199856536430294427 36494542799784804645441641)
      ·
        refine ⟨27370907099838603484081231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36494542799784804645441641 27370907099838603484081231)
        ·
          refine ⟨41056360649757905226121847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27370907099838603484081231 41056360649757905226121847)
          ·
            refine ⟨61584540974636857839182771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41056360649757905226121847 61584540974636857839182771)
            ·
              refine ⟨92376811461955286758774157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61584540974636857839182771 92376811461955286758774157)
              ·
                refine ⟨34641304298233232534540309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92376811461955286758774157 34641304298233232534540309)
                ·
                  refine ⟨1623811138979682775056577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 34641304298233232534540309 1623811138979682775056577)
                  ·
                    refine ⟨1217858354234762081292433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1623811138979682775056577 1217858354234762081292433)
                    ·
                      refine ⟨913393765676071560969325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1217858354234762081292433 913393765676071560969325)
                      ·
                        rfl

theorem cell23_1778828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 6, 2, 2].length) (baseStart_1778828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1778828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1778828 prefixEnd_1778828 := by exact prefixLift 1778828
  have htrace : WordTrace (prefixWord ++ tailWord_1778828) baseStart_1778828 baseEnd_1778828 := by
    simpa [prefixWord, tailWord_1778828, baseEnd_1778828] using wordTrace_append hprefix tailTrace_1778828
  have hstable : (prefixWord ++ tailWord_1778828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778828).length < 2 ^ (prefixWord ++ tailWord_1778828).sum := by decide
  have hdescent : baseEnd_1778828 < baseStart_1778828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778858 : List Nat := [3, 1, 5, 1, 1, 1, 1, 1, 1, 4, 4]
def baseStart_1778858 : Nat := 118140960795 + 1778858 * 2 ^ 59
def prefixEnd_1778858 : Nat := 4983230072969 + 3 ^ 40 * 1778858 * 2
def baseEnd_1778858 : Nat := 913409170095706443594187

theorem tailTrace_1778858 : CollatzResearch.WordTrace tailWord_1778858 prefixEnd_1778858 913409170095706443594187 := by
  unfold tailWord_1778858
  simp only [CollatzResearch.WordTrace]
  refine ⟨16220070347377186401094307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43253520926339163736251485 16220070347377186401094307)
  ·
    refine ⟨24330105521065779601641461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16220070347377186401094307 24330105521065779601641461)
    ·
      refine ⟨2280947392599916837653887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24330105521065779601641461 2280947392599916837653887)
      ·
        refine ⟨3421421088899875256480831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2280947392599916837653887 3421421088899875256480831)
        ·
          refine ⟨5132131633349812884721247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3421421088899875256480831 5132131633349812884721247)
          ·
            refine ⟨7698197450024719327081871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5132131633349812884721247 7698197450024719327081871)
            ·
              refine ⟨11547296175037078990622807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7698197450024719327081871 11547296175037078990622807)
              ·
                refine ⟨17320944262555618485934211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11547296175037078990622807 17320944262555618485934211)
                ·
                  refine ⟨25981416393833427728901317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17320944262555618485934211 25981416393833427728901317)
                  ·
                    refine ⟨4871515573843767699168997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25981416393833427728901317 4871515573843767699168997)
                    ·
                      refine ⟨913409170095706443594187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4871515573843767699168997 913409170095706443594187)
                      ·
                        rfl

theorem cell23_1778858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_1778858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1778858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1778858 prefixEnd_1778858 := by exact prefixLift 1778858
  have htrace : WordTrace (prefixWord ++ tailWord_1778858) baseStart_1778858 baseEnd_1778858 := by
    simpa [prefixWord, tailWord_1778858, baseEnd_1778858] using wordTrace_append hprefix tailTrace_1778858
  have hstable : (prefixWord ++ tailWord_1778858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778858).length < 2 ^ (prefixWord ++ tailWord_1778858).sum := by decide
  have hdescent : baseEnd_1778858 < baseStart_1778858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778864 : List Nat := [2, 1, 1, 1, 2, 1, 2, 3, 3, 7]
def baseStart_1778864 : Nat := 118140960795 + 1778864 * 2 ^ 59
def prefixEnd_1778864 : Nat := 4983230072969 + 3 ^ 40 * 1778864 * 2
def baseEnd_1778864 : Nat := 304470750326544473373053

theorem tailTrace_1778864 : CollatzResearch.WordTrace tailWord_1778864 prefixEnd_1778864 304470750326544473373053 := by
  unfold tailWord_1778864
  simp only [CollatzResearch.WordTrace]
  refine ⟨32440250113743504314547823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43253666818324672419397097 32440250113743504314547823)
  ·
    refine ⟨48660375170615256471821735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32440250113743504314547823 48660375170615256471821735)
    ·
      refine ⟨72990562755922884707732603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48660375170615256471821735 72990562755922884707732603)
      ·
        refine ⟨109485844133884327061598905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72990562755922884707732603 109485844133884327061598905)
        ·
          refine ⟨82114383100413245296199179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109485844133884327061598905 82114383100413245296199179)
          ·
            refine ⟨123171574650619867944298769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82114383100413245296199179 123171574650619867944298769)
            ·
              refine ⟨92378680987964900958224077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123171574650619867944298769 92378680987964900958224077)
              ·
                refine ⟨34642005370486837859334029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92378680987964900958224077 34642005370486837859334029)
                ·
                  refine ⟨12990752013932564197250261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34642005370486837859334029 12990752013932564197250261)
                  ·
                    refine ⟨304470750326544473373053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12990752013932564197250261 304470750326544473373053)
                    ·
                      rfl

theorem cell23_1778864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 3, 7].length) (baseStart_1778864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1778864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1778864 prefixEnd_1778864 := by exact prefixLift 1778864
  have htrace : WordTrace (prefixWord ++ tailWord_1778864) baseStart_1778864 baseEnd_1778864 := by
    simpa [prefixWord, tailWord_1778864, baseEnd_1778864] using wordTrace_append hprefix tailTrace_1778864
  have hstable : (prefixWord ++ tailWord_1778864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778864).length < 2 ^ (prefixWord ++ tailWord_1778864).sum := by decide
  have hdescent : baseEnd_1778864 < baseStart_1778864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778938 : List Nat := [3, 1, 1, 1, 1, 4, 2, 3, 2, 2, 3]
def baseStart_1778938 : Nat := 118140960795 + 1778938 * 2 ^ 59
def prefixEnd_1778938 : Nat := 4983230072969 + 3 ^ 40 * 1778938 * 2
def baseEnd_1778938 : Nat := 913450248548066130593819

theorem tailTrace_1778938 : CollatzResearch.WordTrace tailWord_1778938 prefixEnd_1778938 913450248548066130593819 := by
  unfold tailWord_1778938
  simp only [CollatzResearch.WordTrace]
  refine ⟨16220799807304729816822367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43255466152812612844859645 16220799807304729816822367)
  ·
    refine ⟨24331199710957094725233551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16220799807304729816822367 24331199710957094725233551)
    ·
      refine ⟨36496799566435642087850327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24331199710957094725233551 36496799566435642087850327)
      ·
        refine ⟨54745199349653463131775491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36496799566435642087850327 54745199349653463131775491)
        ·
          refine ⟨82117799024480194697663237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54745199349653463131775491 82117799024480194697663237)
          ·
            refine ⟨15397087317090036505811857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82117799024480194697663237 15397087317090036505811857)
            ·
              refine ⟨11547815487817527379358893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15397087317090036505811857 11547815487817527379358893)
              ·
                refine ⟨4330430807931572767259585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11547815487817527379358893 4330430807931572767259585)
                ·
                  refine ⟨3247823105948679575444689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4330430807931572767259585 3247823105948679575444689)
                  ·
                    refine ⟨2435867329461509681583517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3247823105948679575444689 2435867329461509681583517)
                    ·
                      refine ⟨913450248548066130593819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2435867329461509681583517 913450248548066130593819)
                      ·
                        rfl

theorem cell23_1778938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3, 2, 2, 3].length) (baseStart_1778938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1778938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1778938 prefixEnd_1778938 := by exact prefixLift 1778938
  have htrace : WordTrace (prefixWord ++ tailWord_1778938) baseStart_1778938 baseEnd_1778938 := by
    simpa [prefixWord, tailWord_1778938, baseEnd_1778938] using wordTrace_append hprefix tailTrace_1778938
  have hstable : (prefixWord ++ tailWord_1778938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778938).length < 2 ^ (prefixWord ++ tailWord_1778938).sum := by decide
  have hdescent : baseEnd_1778938 < baseStart_1778938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778971 : List Nat := [1, 1, 1, 1, 1, 1, 5, 4, 3, 5]
def baseStart_1778971 : Nat := 118140960795 + 1778971 * 2 ^ 59
def prefixEnd_1778971 : Nat := 4983230072969 + 3 ^ 40 * 1778971 * 2
def baseEnd_1778971 : Nat := 304489064469888167160389

theorem tailTrace_1778971 : CollatzResearch.WordTrace tailWord_1778971 prefixEnd_1778971 304489064469888167160389 := by
  unfold tailWord_1778971
  simp only [CollatzResearch.WordTrace]
  refine ⟨64884402838099365903240767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43256268558732910602160511 64884402838099365903240767)
  ·
    refine ⟨97326604257149048854861151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64884402838099365903240767 97326604257149048854861151)
    ·
      refine ⟨145989906385723573282291727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97326604257149048854861151 145989906385723573282291727)
      ·
        refine ⟨218984859578585359923437591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145989906385723573282291727 218984859578585359923437591)
        ·
          refine ⟨328477289367878039885156387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218984859578585359923437591 328477289367878039885156387)
          ·
            refine ⟨492715934051817059827734581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328477289367878039885156387 492715934051817059827734581)
            ·
              refine ⟨46192118817357849358850117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 492715934051817059827734581 46192118817357849358850117)
              ·
                refine ⟨8661022278254596754784397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46192118817357849358850117 8661022278254596754784397)
                ·
                  refine ⟨3247883354345473783044149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8661022278254596754784397 3247883354345473783044149)
                  ·
                    refine ⟨304489064469888167160389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3247883354345473783044149 304489064469888167160389)
                    ·
                      rfl

theorem cell23_1778971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 3, 5].length) (baseStart_1778971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1778971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1778971 prefixEnd_1778971 := by exact prefixLift 1778971
  have htrace : WordTrace (prefixWord ++ tailWord_1778971) baseStart_1778971 baseEnd_1778971 := by
    simpa [prefixWord, tailWord_1778971, baseEnd_1778971] using wordTrace_append hprefix tailTrace_1778971
  have hstable : (prefixWord ++ tailWord_1778971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778971).length < 2 ^ (prefixWord ++ tailWord_1778971).sum := by decide
  have hdescent : baseEnd_1778971 < baseStart_1778971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1778995 : List Nat := [1, 1, 1, 2, 5, 2, 1, 3, 2, 3, 2]
def baseStart_1778995 : Nat := 118140960795 + 1778995 * 2 ^ 59
def prefixEnd_1778995 : Nat := 4983230072969 + 3 ^ 40 * 1778995 * 2
def baseEnd_1778995 : Nat := 913479516945372407581057

theorem tailTrace_1778995 : CollatzResearch.WordTrace tailWord_1778995 prefixEnd_1778995 913479516945372407581057 := by
  unfold tailWord_1778995
  simp only [CollatzResearch.WordTrace]
  refine ⟨64885278190012418002114439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43256852126674945334742959 64885278190012418002114439)
  ·
    refine ⟨97327917285018627003171659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64885278190012418002114439 97327917285018627003171659)
    ·
      refine ⟨145991875927527940504757489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97327917285018627003171659 145991875927527940504757489)
      ·
        refine ⟨109493906945645955378568117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145991875927527940504757489 109493906945645955378568117)
        ·
          refine ⟨10265053776154308316740761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 109493906945645955378568117 10265053776154308316740761)
          ·
            refine ⟨7698790332115731237555571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10265053776154308316740761 7698790332115731237555571)
            ·
              refine ⟨11548185498173596856333357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7698790332115731237555571 11548185498173596856333357)
              ·
                refine ⟨4330569561815098821125009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11548185498173596856333357 4330569561815098821125009)
                ·
                  refine ⟨3247927171361324115843757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4330569561815098821125009 3247927171361324115843757)
                  ·
                    refine ⟨1217972689260496543441409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3247927171361324115843757 1217972689260496543441409)
                    ·
                      refine ⟨913479516945372407581057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1217972689260496543441409 913479516945372407581057)
                      ·
                        rfl

theorem cell23_1778995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3, 2, 3, 2].length) (baseStart_1778995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1778995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1778995 prefixEnd_1778995 := by exact prefixLift 1778995
  have htrace : WordTrace (prefixWord ++ tailWord_1778995) baseStart_1778995 baseEnd_1778995 := by
    simpa [prefixWord, tailWord_1778995, baseEnd_1778995] using wordTrace_append hprefix tailTrace_1778995
  have hstable : (prefixWord ++ tailWord_1778995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1778995).length < 2 ^ (prefixWord ++ tailWord_1778995).sum := by decide
  have hdescent : baseEnd_1778995 < baseStart_1778995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1778995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779002 : List Nat := [3, 1, 1, 1, 4, 1, 2, 5, 1, 1, 3]
def baseStart_1779002 : Nat := 118140960795 + 1779002 * 2 ^ 59
def prefixEnd_1779002 : Nat := 4983230072969 + 3 ^ 40 * 1779002 * 2
def baseEnd_1779002 : Nat := 913483111309953880193525

theorem tailTrace_1779002 : CollatzResearch.WordTrace tailWord_1779002 prefixEnd_1779002 913483111309953880193525 := by
  unfold tailWord_1779002
  simp only [CollatzResearch.WordTrace]
  refine ⟨16221383375246764549404815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43257022333991372131746173 16221383375246764549404815)
  ·
    refine ⟨24332075062870146824107223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16221383375246764549404815 24332075062870146824107223)
    ·
      refine ⟨36498112594305220236160835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24332075062870146824107223 36498112594305220236160835)
      ·
        refine ⟨54747168891457830354241253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36498112594305220236160835 54747168891457830354241253)
        ·
          refine ⟨10265094167148343191420235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54747168891457830354241253 10265094167148343191420235)
          ·
            refine ⟨15397641250722514787130353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10265094167148343191420235 15397641250722514787130353)
            ·
              refine ⟨11548230938041886090347765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15397641250722514787130353 11548230938041886090347765)
              ·
                refine ⟨1082646650441426820970103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11548230938041886090347765 1082646650441426820970103)
                ·
                  refine ⟨1623969975662140231455155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1082646650441426820970103 1623969975662140231455155)
                  ·
                    refine ⟨2435954963493210347182733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1623969975662140231455155 2435954963493210347182733)
                    ·
                      refine ⟨913483111309953880193525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2435954963493210347182733 913483111309953880193525)
                      ·
                        rfl

theorem cell23_1779002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 5, 1, 1, 3].length) (baseStart_1779002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1779002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1779002 prefixEnd_1779002 := by exact prefixLift 1779002
  have htrace : WordTrace (prefixWord ++ tailWord_1779002) baseStart_1779002 baseEnd_1779002 := by
    simpa [prefixWord, tailWord_1779002, baseEnd_1779002] using wordTrace_append hprefix tailTrace_1779002
  have hstable : (prefixWord ++ tailWord_1779002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779002).length < 2 ^ (prefixWord ++ tailWord_1779002).sum := by decide
  have hdescent : baseEnd_1779002 < baseStart_1779002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779018 : List Nat := [3, 1, 2, 1, 1, 1, 1, 5, 4, 4]
def baseStart_1779018 : Nat := 118140960795 + 1779018 * 2 ^ 59
def prefixEnd_1779018 : Nat := 4983230072969 + 3 ^ 40 * 1779018 * 2
def baseEnd_1779018 : Nat := 304497109000141939197817

theorem tailTrace_1779018 : CollatzResearch.WordTrace tailWord_1779018 prefixEnd_1779018 304497109000141939197817 := by
  unfold tailWord_1779018
  simp only [CollatzResearch.WordTrace]
  refine ⟨16221529267232273232550427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43257411379286061953467805 16221529267232273232550427)
  ·
    refine ⟨24332293900848409848825641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16221529267232273232550427 24332293900848409848825641)
    ·
      refine ⟨18249220425636307386619231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24332293900848409848825641 18249220425636307386619231)
      ·
        refine ⟨27373830638454461079928847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18249220425636307386619231 27373830638454461079928847)
        ·
          refine ⟨41060745957681691619893271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27373830638454461079928847 41060745957681691619893271)
          ·
            refine ⟨61591118936522537429839907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41060745957681691619893271 61591118936522537429839907)
            ·
              refine ⟨92386678404783806144759861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61591118936522537429839907 92386678404783806144759861)
              ·
                refine ⟨8661251100448481826071237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92386678404783806144759861 8661251100448481826071237)
                ·
                  refine ⟨1623984581334090342388357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8661251100448481826071237 1623984581334090342388357)
                  ·
                    refine ⟨304497109000141939197817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1623984581334090342388357 304497109000141939197817)
                    ·
                      rfl

theorem cell23_1779018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 4, 4].length) (baseStart_1779018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1779018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1779018 prefixEnd_1779018 := by exact prefixLift 1779018
  have htrace : WordTrace (prefixWord ++ tailWord_1779018) baseStart_1779018 baseEnd_1779018 := by
    simpa [prefixWord, tailWord_1779018, baseEnd_1779018] using wordTrace_append hprefix tailTrace_1779018
  have hstable : (prefixWord ++ tailWord_1779018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779018).length < 2 ^ (prefixWord ++ tailWord_1779018).sum := by decide
  have hdescent : baseEnd_1779018 < baseStart_1779018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779028 : List Nat := [2, 4, 1, 1, 2, 1, 2, 1, 3, 1, 5]
def baseStart_1779028 : Nat := 118140960795 + 1779028 * 2 ^ 59
def prefixEnd_1779028 : Nat := 4983230072969 + 3 ^ 40 * 1779028 * 2
def baseEnd_1779028 : Nat := 913496461806970778468405

theorem tailTrace_1779028 : CollatzResearch.WordTrace tailWord_1779028 prefixEnd_1779028 913496461806970778468405 := by
  unfold tailWord_1779028
  simp only [CollatzResearch.WordTrace]
  refine ⟨32443240899446432319032869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43257654532595243092043825 32443240899446432319032869)
  ·
    refine ⟨6083107668646206059818663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32443240899446432319032869 6083107668646206059818663)
    ·
      refine ⟨9124661502969309089727995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6083107668646206059818663 9124661502969309089727995)
      ·
        refine ⟨13686992254453963634591993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9124661502969309089727995 13686992254453963634591993)
        ·
          refine ⟨10265244190840472725943995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13686992254453963634591993 10265244190840472725943995)
          ·
            refine ⟨15397866286260709088915993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10265244190840472725943995 15397866286260709088915993)
            ·
              refine ⟨11548399714695531816686995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15397866286260709088915993 11548399714695531816686995)
              ·
                refine ⟨17322599572043297725030493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11548399714695531816686995 17322599572043297725030493)
                ·
                  refine ⟨6495974839516236646886435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17322599572043297725030493 6495974839516236646886435)
                  ·
                    refine ⟨9743962259274354970329653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6495974839516236646886435 9743962259274354970329653)
                    ·
                      refine ⟨913496461806970778468405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9743962259274354970329653 913496461806970778468405)
                      ·
                        rfl

theorem cell23_1779028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_1779028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1779028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1779028 prefixEnd_1779028 := by exact prefixLift 1779028
  have htrace : WordTrace (prefixWord ++ tailWord_1779028) baseStart_1779028 baseEnd_1779028 := by
    simpa [prefixWord, tailWord_1779028, baseEnd_1779028] using wordTrace_append hprefix tailTrace_1779028
  have hstable : (prefixWord ++ tailWord_1779028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779028).length < 2 ^ (prefixWord ++ tailWord_1779028).sum := by decide
  have hdescent : baseEnd_1779028 < baseStart_1779028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779041 : List Nat := [1, 2, 3, 1, 1, 1, 1, 2, 2, 2, 7]
def baseStart_1779041 : Nat := 118140960795 + 1779041 * 2 ^ 59
def prefixEnd_1779041 : Nat := 4983230072969 + 3 ^ 40 * 1779041 * 2
def baseEnd_1779041 : Nat := 913503137055479227605845

theorem tailTrace_1779041 : CollatzResearch.WordTrace tailWord_1779041 prefixEnd_1779041 913503137055479227605845 := by
  unfold tailWord_1779041
  simp only [CollatzResearch.WordTrace]
  refine ⟨64886955947845767858288977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43257970631897178572192651 64886955947845767858288977)
  ·
    refine ⟨48665216960884325893716733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64886955947845767858288977 48665216960884325893716733)
    ·
      refine ⟨18249456360331622210143775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48665216960884325893716733 18249456360331622210143775)
      ·
        refine ⟨27374184540497433315215663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18249456360331622210143775 27374184540497433315215663)
        ·
          refine ⟨41061276810746149972823495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27374184540497433315215663 41061276810746149972823495)
          ·
            refine ⟨61591915216119224959235243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41061276810746149972823495 61591915216119224959235243)
            ·
              refine ⟨92387872824178837438852865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61591915216119224959235243 92387872824178837438852865)
              ·
                refine ⟨69290904618134128079139649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92387872824178837438852865 69290904618134128079139649)
                ·
                  refine ⟨51968178463600596059354737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69290904618134128079139649 51968178463600596059354737)
                  ·
                    refine ⟨38976133847700447044516053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51968178463600596059354737 38976133847700447044516053)
                    ·
                      refine ⟨913503137055479227605845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 38976133847700447044516053 913503137055479227605845)
                      ·
                        rfl

theorem cell23_1779041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_1779041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1779041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1779041 prefixEnd_1779041 := by exact prefixLift 1779041
  have htrace : WordTrace (prefixWord ++ tailWord_1779041) baseStart_1779041 baseEnd_1779041 := by
    simpa [prefixWord, tailWord_1779041, baseEnd_1779041] using wordTrace_append hprefix tailTrace_1779041
  have hstable : (prefixWord ++ tailWord_1779041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779041).length < 2 ^ (prefixWord ++ tailWord_1779041).sum := by decide
  have hdescent : baseEnd_1779041 < baseStart_1779041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779045 : List Nat := [1, 3, 1, 3, 1, 2, 2, 4, 1, 2, 3]
def baseStart_1779045 : Nat := 118140960795 + 1779045 * 2 ^ 59
def prefixEnd_1779045 : Nat := 4983230072969 + 3 ^ 40 * 1779045 * 2
def baseEnd_1779045 : Nat := 913505190978097211955827

theorem tailTrace_1779045 : CollatzResearch.WordTrace tailWord_1779045 prefixEnd_1779045 913505190978097211955827 := by
  unfold tailWord_1779045
  simp only [CollatzResearch.WordTrace]
  refine ⟨64887101839831276541434589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43258067893220851027623059 64887101839831276541434589)
  ·
    refine ⟨24332663189936728703037971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64887101839831276541434589 24332663189936728703037971)
    ·
      refine ⟨36498994784905093054556957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24332663189936728703037971 36498994784905093054556957)
      ·
        refine ⟨13687123044339409895458859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36498994784905093054556957 13687123044339409895458859)
        ·
          refine ⟨20530684566509114843188289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13687123044339409895458859 20530684566509114843188289)
          ·
            refine ⟨15398013424881836132391217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20530684566509114843188289 15398013424881836132391217)
            ·
              refine ⟨11548510068661377099293413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15398013424881836132391217 11548510068661377099293413)
              ·
                refine ⟨2165345637874008206117515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11548510068661377099293413 2165345637874008206117515)
                ·
                  refine ⟨3248018456811012309176273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2165345637874008206117515 3248018456811012309176273)
                  ·
                    refine ⟨2436013842608259231882205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3248018456811012309176273 2436013842608259231882205)
                    ·
                      refine ⟨913505190978097211955827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2436013842608259231882205 913505190978097211955827)
                      ·
                        rfl

theorem cell23_1779045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_1779045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1779045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1779045 prefixEnd_1779045 := by exact prefixLift 1779045
  have htrace : WordTrace (prefixWord ++ tailWord_1779045) baseStart_1779045 baseEnd_1779045 := by
    simpa [prefixWord, tailWord_1779045, baseEnd_1779045] using wordTrace_append hprefix tailTrace_1779045
  have hstable : (prefixWord ++ tailWord_1779045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779045).length < 2 ^ (prefixWord ++ tailWord_1779045).sum := by decide
  have hdescent : baseEnd_1779045 < baseStart_1779045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779071 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 7]
def baseStart_1779071 : Nat := 118140960795 + 1779071 * 2 ^ 59
def prefixEnd_1779071 : Nat := 4983230072969 + 3 ^ 40 * 1779071 * 2
def baseEnd_1779071 : Nat := 913518541475114110230707

theorem tailTrace_1779071 : CollatzResearch.WordTrace tailWord_1779071 prefixEnd_1779071 913518541475114110230707 := by
  unfold tailWord_1779071
  simp only [CollatzResearch.WordTrace]
  refine ⟨64888050137737082981881067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43258700091824721987920711 64888050137737082981881067)
  ·
    refine ⟨97332075206605624472821601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64888050137737082981881067 97332075206605624472821601)
    ·
      refine ⟨72999056404954218354616201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97332075206605624472821601 72999056404954218354616201)
      ·
        refine ⟨54749292303715663765962151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72999056404954218354616201 54749292303715663765962151)
        ·
          refine ⟨82123938455573495648943227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54749292303715663765962151 82123938455573495648943227)
          ·
            refine ⟨123185907683360243473414841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82123938455573495648943227 123185907683360243473414841)
            ·
              refine ⟨92389430762520182605061131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123185907683360243473414841 92389430762520182605061131)
              ·
                refine ⟨138584146143780273907591697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92389430762520182605061131 138584146143780273907591697)
                ·
                  refine ⟨103938109607835205430693773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138584146143780273907591697 103938109607835205430693773)
                  ·
                    refine ⟨38976791102938202036510165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 103938109607835205430693773 38976791102938202036510165)
                    ·
                      refine ⟨913518541475114110230707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 38976791102938202036510165 913518541475114110230707)
                      ·
                        rfl

theorem cell23_1779071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 7].length) (baseStart_1779071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1779071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1779071 prefixEnd_1779071 := by exact prefixLift 1779071
  have htrace : WordTrace (prefixWord ++ tailWord_1779071) baseStart_1779071 baseEnd_1779071 := by
    simpa [prefixWord, tailWord_1779071, baseEnd_1779071] using wordTrace_append hprefix tailTrace_1779071
  have hstable : (prefixWord ++ tailWord_1779071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779071).length < 2 ^ (prefixWord ++ tailWord_1779071).sum := by decide
  have hdescent : baseEnd_1779071 < baseStart_1779071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779092 : List Nat := [2, 4, 2, 1, 2, 1, 3, 1, 1, 3, 3]
def baseStart_1779092 : Nat := 118140960795 + 1779092 * 2 ^ 59
def prefixEnd_1779092 : Nat := 4983230072969 + 3 ^ 40 * 1779092 * 2
def baseEnd_1779092 : Nat := 913529324568858528068111

theorem tailTrace_1779092 : CollatzResearch.WordTrace tailWord_1779092 prefixEnd_1779092 913529324568858528068111 := by
  unfold tailWord_1779092
  simp only [CollatzResearch.WordTrace]
  refine ⟨32444408035330501784197765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43259210713774002378930353 32444408035330501784197765)
  ·
    refine ⟨6083326506624469084537081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32444408035330501784197765 6083326506624469084537081)
    ·
      refine ⟨4562494879968351813402811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6083326506624469084537081 4562494879968351813402811)
      ·
        refine ⟨6843742319952527720104217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4562494879968351813402811 6843742319952527720104217)
        ·
          refine ⟨5132806739964395790078163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6843742319952527720104217 5132806739964395790078163)
          ·
            refine ⟨7699210109946593685117245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5132806739964395790078163 7699210109946593685117245)
            ·
              refine ⟨2887203791229972631918967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7699210109946593685117245 2887203791229972631918967)
              ·
                refine ⟨4330805686844958947878451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2887203791229972631918967 4330805686844958947878451)
                ·
                  refine ⟨6496208530267438421817677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4330805686844958947878451 6496208530267438421817677)
                  ·
                    refine ⟨2436078198850289408181629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6496208530267438421817677 2436078198850289408181629)
                    ·
                      refine ⟨913529324568858528068111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2436078198850289408181629 913529324568858528068111)
                      ·
                        rfl

theorem cell23_1779092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_1779092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1779092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1779092 prefixEnd_1779092 := by exact prefixLift 1779092
  have htrace : WordTrace (prefixWord ++ tailWord_1779092) baseStart_1779092 baseEnd_1779092 := by
    simpa [prefixWord, tailWord_1779092, baseEnd_1779092] using wordTrace_append hprefix tailTrace_1779092
  have hstable : (prefixWord ++ tailWord_1779092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779092).length < 2 ^ (prefixWord ++ tailWord_1779092).sum := by decide
  have hdescent : baseEnd_1779092 < baseStart_1779092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779128 : List Nat := [2, 1, 2, 1, 2, 2, 2, 1, 4, 2, 4]
def baseStart_1779128 : Nat := 118140960795 + 1779128 * 2 ^ 59
def prefixEnd_1779128 : Nat := 4983230072969 + 3 ^ 40 * 1779128 * 2
def baseEnd_1779128 : Nat := 913547809872420387217945

theorem tailTrace_1779128 : CollatzResearch.WordTrace tailWord_1779128 prefixEnd_1779128 913547809872420387217945 := by
  unfold tailWord_1779128
  simp only [CollatzResearch.WordTrace]
  refine ⟨32445064549265290858353019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43260086065687054477804025 32445064549265290858353019)
  ·
    refine ⟨48667596823897936287529529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32445064549265290858353019 48667596823897936287529529)
    ·
      refine ⟨36500697617923452215647147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48667596823897936287529529 36500697617923452215647147)
      ·
        refine ⟨54751046426885178323470721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36500697617923452215647147 54751046426885178323470721)
        ·
          refine ⟨41063284820163883742603041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54751046426885178323470721 41063284820163883742603041)
          ·
            refine ⟨30797463615122912806952281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41063284820163883742603041 30797463615122912806952281)
            ·
              refine ⟨23098097711342184605214211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30797463615122912806952281 23098097711342184605214211)
              ·
                refine ⟨34647146567013276907821317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23098097711342184605214211 34647146567013276907821317)
                ·
                  refine ⟨6496339981314989420216497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34647146567013276907821317 6496339981314989420216497)
                  ·
                    refine ⟨4872254985986242065162373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6496339981314989420216497 4872254985986242065162373)
                    ·
                      refine ⟨913547809872420387217945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4872254985986242065162373 913547809872420387217945)
                      ·
                        rfl

theorem cell23_1779128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 4, 2, 4].length) (baseStart_1779128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1779128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1779128 prefixEnd_1779128 := by exact prefixLift 1779128
  have htrace : WordTrace (prefixWord ++ tailWord_1779128) baseStart_1779128 baseEnd_1779128 := by
    simpa [prefixWord, tailWord_1779128, baseEnd_1779128] using wordTrace_append hprefix tailTrace_1779128
  have hstable : (prefixWord ++ tailWord_1779128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779128).length < 2 ^ (prefixWord ++ tailWord_1779128).sum := by decide
  have hdescent : baseEnd_1779128 < baseStart_1779128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779185 : List Nat := [1, 2, 2, 2, 3, 2, 2, 2, 2, 5]
def baseStart_1779185 : Nat := 118140960795 + 1779185 * 2 ^ 59
def prefixEnd_1779185 : Nat := 4983230072969 + 3 ^ 40 * 1779185 * 2
def baseEnd_1779185 : Nat := 304525692756575554735061

theorem tailTrace_1779185 : CollatzResearch.WordTrace tailWord_1779185 prefixEnd_1779185 304525692756575554735061 := by
  unfold tailWord_1779185
  simp only [CollatzResearch.WordTrace]
  refine ⟨64892208059324080451531009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43261472039549386967687339 64892208059324080451531009)
  ·
    refine ⟨48669156044493060338648257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64892208059324080451531009 48669156044493060338648257)
    ·
      refine ⟨36501867033369795253986193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48669156044493060338648257 36501867033369795253986193)
      ·
        refine ⟨27376400275027346440489645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36501867033369795253986193 27376400275027346440489645)
        ·
          refine ⟨10266150103135254915183617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27376400275027346440489645 10266150103135254915183617)
          ·
            refine ⟨7699612577351441186387713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10266150103135254915183617 7699612577351441186387713)
            ·
              refine ⟨5774709433013580889790785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7699612577351441186387713 5774709433013580889790785)
              ·
                refine ⟨4331032074760185667343089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5774709433013580889790785 4331032074760185667343089)
                ·
                  refine ⟨3248274056070139250507317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4331032074760185667343089 3248274056070139250507317)
                  ·
                    refine ⟨304525692756575554735061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3248274056070139250507317 304525692756575554735061)
                    ·
                      rfl

theorem cell23_1779185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 2, 5].length) (baseStart_1779185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1779185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1779185 prefixEnd_1779185 := by exact prefixLift 1779185
  have htrace : WordTrace (prefixWord ++ tailWord_1779185) baseStart_1779185 baseEnd_1779185 := by
    simpa [prefixWord, tailWord_1779185, baseEnd_1779185] using wordTrace_append hprefix tailTrace_1779185
  have hstable : (prefixWord ++ tailWord_1779185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779185).length < 2 ^ (prefixWord ++ tailWord_1779185).sum := by decide
  have hdescent : baseEnd_1779185 < baseStart_1779185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779189 : List Nat := [1, 3, 5, 1, 1, 2, 1, 4, 5]
def baseStart_1779189 : Nat := 118140960795 + 1779189 * 2 ^ 59
def prefixEnd_1779189 : Nat := 4983230072969 + 3 ^ 40 * 1779189 * 2
def baseEnd_1779189 : Nat := 101508792465816072061685

theorem tailTrace_1779189 : CollatzResearch.WordTrace tailWord_1779189 prefixEnd_1779189 101508792465816072061685 := by
  unfold tailWord_1779189
  simp only [CollatzResearch.WordTrace]
  refine ⟨64892353951309589134676621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43261569300873059423117747 64892353951309589134676621)
  ·
    refine ⟨24334632731741095925503733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64892353951309589134676621 24334632731741095925503733)
    ·
      refine ⟨2281371818600727743015975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24334632731741095925503733 2281371818600727743015975)
      ·
        refine ⟨3422057727901091614523963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2281371818600727743015975 3422057727901091614523963)
        ·
          refine ⟨5133086591851637421785945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3422057727901091614523963 5133086591851637421785945)
          ·
            refine ⟨3849814943888728066339459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5133086591851637421785945 3849814943888728066339459)
            ·
              refine ⟨5774722415833092099509189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3849814943888728066339459 5774722415833092099509189)
              ·
                refine ⟨1082760452968704768657973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5774722415833092099509189 1082760452968704768657973)
                ·
                  refine ⟨101508792465816072061685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1082760452968704768657973 101508792465816072061685)
                  ·
                    rfl

theorem cell23_1779189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 4, 5].length) (baseStart_1779189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1779189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1779189 prefixEnd_1779189 := by exact prefixLift 1779189
  have htrace : WordTrace (prefixWord ++ tailWord_1779189) baseStart_1779189 baseEnd_1779189 := by
    simpa [prefixWord, tailWord_1779189, baseEnd_1779189] using wordTrace_append hprefix tailTrace_1779189
  have hstable : (prefixWord ++ tailWord_1779189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779189).length < 2 ^ (prefixWord ++ tailWord_1779189).sum := by decide
  have hdescent : baseEnd_1779189 < baseStart_1779189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779206 : List Nat := [6, 2, 1, 1, 2, 1, 1, 2, 7]
def baseStart_1779206 : Nat := 118140960795 + 1779206 * 2 ^ 59
def prefixEnd_1779206 : Nat := 4983230072969 + 3 ^ 40 * 1779206 * 2
def baseEnd_1779206 : Nat := 101509762373719009115843

theorem tailTrace_1779206 : CollatzResearch.WordTrace tailWord_1779206 prefixEnd_1779206 101509762373719009115843 := by
  unfold tailWord_1779206
  simp only [CollatzResearch.WordTrace]
  refine ⟨2027905437257750032438921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 43261982661498667358696981 2027905437257750032438921)
  ·
    refine ⟨1520929077943312524329191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2027905437257750032438921 1520929077943312524329191)
    ·
      refine ⟨2281393616914968786493787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1520929077943312524329191 2281393616914968786493787)
      ·
        refine ⟨3422090425372453179740681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2281393616914968786493787 3422090425372453179740681)
        ·
          refine ⟨2566567819029339884805511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3422090425372453179740681 2566567819029339884805511)
          ·
            refine ⟨3849851728544009827208267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2566567819029339884805511 3849851728544009827208267)
            ·
              refine ⟨5774777592816014740812401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3849851728544009827208267 5774777592816014740812401)
              ·
                refine ⟨4331083194612011055609301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5774777592816014740812401 4331083194612011055609301)
                ·
                  refine ⟨101509762373719009115843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4331083194612011055609301 101509762373719009115843)
                  ·
                    rfl

theorem cell23_1779206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_1779206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1779206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1779206 prefixEnd_1779206 := by exact prefixLift 1779206
  have htrace : WordTrace (prefixWord ++ tailWord_1779206) baseStart_1779206 baseEnd_1779206 := by
    simpa [prefixWord, tailWord_1779206, baseEnd_1779206] using wordTrace_append hprefix tailTrace_1779206
  have hstable : (prefixWord ++ tailWord_1779206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779206).length < 2 ^ (prefixWord ++ tailWord_1779206).sum := by decide
  have hdescent : baseEnd_1779206 < baseStart_1779206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779242 : List Nat := [3, 1, 4, 1, 1, 1, 2, 1, 4, 2, 3]
def baseStart_1779242 : Nat := 118140960795 + 1779242 * 2 ^ 59
def prefixEnd_1779242 : Nat := 4983230072969 + 3 ^ 40 * 1779242 * 2
def baseEnd_1779242 : Nat := 913606346667032941192421

theorem tailTrace_1779242 : CollatzResearch.WordTrace tailWord_1779242 prefixEnd_1779242 913606346667032941192421 := by
  unfold tailWord_1779242
  simp only [CollatzResearch.WordTrace]
  refine ⟨16223571755029394796588995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43262858013411719457570653 16223571755029394796588995)
  ·
    refine ⟨24335357632544092194883493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16223571755029394796588995 24335357632544092194883493)
    ·
      refine ⟨4562879556102017286540655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24335357632544092194883493 4562879556102017286540655)
      ·
        refine ⟨6844319334153025929810983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4562879556102017286540655 6844319334153025929810983)
        ·
          refine ⟨10266479001229538894716475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6844319334153025929810983 10266479001229538894716475)
          ·
            refine ⟨15399718501844308342074713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10266479001229538894716475 15399718501844308342074713)
            ·
              refine ⟨11549788876383231256556035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15399718501844308342074713 11549788876383231256556035)
              ·
                refine ⟨17324683314574846884834053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11549788876383231256556035 17324683314574846884834053)
                ·
                  refine ⟨3248378121482783790906385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17324683314574846884834053 3248378121482783790906385)
                  ·
                    refine ⟨2436283591112087843179789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3248378121482783790906385 2436283591112087843179789)
                    ·
                      refine ⟨913606346667032941192421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2436283591112087843179789 913606346667032941192421)
                      ·
                        rfl

theorem cell23_1779242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_1779242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1779242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1779242 prefixEnd_1779242 := by exact prefixLift 1779242
  have htrace : WordTrace (prefixWord ++ tailWord_1779242) baseStart_1779242 baseEnd_1779242 := by
    simpa [prefixWord, tailWord_1779242, baseEnd_1779242] using wordTrace_append hprefix tailTrace_1779242
  have hstable : (prefixWord ++ tailWord_1779242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779242).length < 2 ^ (prefixWord ++ tailWord_1779242).sum := by decide
  have hdescent : baseEnd_1779242 < baseStart_1779242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779265 : List Nat := [1, 2, 5, 1, 1, 1, 1, 2, 1, 2, 6]
def baseStart_1779265 : Nat := 118140960795 + 1779265 * 2 ^ 59
def prefixEnd_1779265 : Nat := 4983230072969 + 3 ^ 40 * 1779265 * 2
def baseEnd_1779265 : Nat := 913618156722086351204815

theorem tailTrace_1779265 : CollatzResearch.WordTrace tailWord_1779265 prefixEnd_1779265 913618156722086351204815 := by
  unfold tailWord_1779265
  simp only [CollatzResearch.WordTrace]
  refine ⟨64895125899034254114443249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43263417266022836076295499 64895125899034254114443249)
  ·
    refine ⟨48671344424275690585832437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64895125899034254114443249 48671344424275690585832437)
    ·
      refine ⟨4562938539775845992421791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48671344424275690585832437 4562938539775845992421791)
      ·
        refine ⟨6844407809663768988632687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4562938539775845992421791 6844407809663768988632687)
        ·
          refine ⟨10266611714495653482949031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6844407809663768988632687 10266611714495653482949031)
          ·
            refine ⟨15399917571743480224423547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10266611714495653482949031 15399917571743480224423547)
            ·
              refine ⟨23099876357615220336635321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15399917571743480224423547 23099876357615220336635321)
              ·
                refine ⟨17324907268211415252476491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23099876357615220336635321 17324907268211415252476491)
                ·
                  refine ⟨25987360902317122878714737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17324907268211415252476491 25987360902317122878714737)
                  ·
                    refine ⟨19490520676737842159036053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25987360902317122878714737 19490520676737842159036053)
                    ·
                      refine ⟨913618156722086351204815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19490520676737842159036053 913618156722086351204815)
                      ·
                        rfl

theorem cell23_1779265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_1779265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1779265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1779265 prefixEnd_1779265 := by exact prefixLift 1779265
  have htrace : WordTrace (prefixWord ++ tailWord_1779265) baseStart_1779265 baseEnd_1779265 := by
    simpa [prefixWord, tailWord_1779265, baseEnd_1779265] using wordTrace_append hprefix tailTrace_1779265
  have hstable : (prefixWord ++ tailWord_1779265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779265).length < 2 ^ (prefixWord ++ tailWord_1779265).sum := by decide
  have hdescent : baseEnd_1779265 < baseStart_1779265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779295 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 7, 1, 4]
def baseStart_1779295 : Nat := 118140960795 + 1779295 * 2 ^ 59
def prefixEnd_1779295 : Nat := 4983230072969 + 3 ^ 40 * 1779295 * 2
def baseEnd_1779295 : Nat := 913633561141721233829677

theorem tailTrace_1779295 : CollatzResearch.WordTrace tailWord_1779295 prefixEnd_1779295 913633561141721233829677 := by
  unfold tailWord_1779295
  simp only [CollatzResearch.WordTrace]
  refine ⟨64896220088925569238035339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43264146725950379492023559 64896220088925569238035339)
  ·
    refine ⟨97344330133388353857053009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64896220088925569238035339 97344330133388353857053009)
    ·
      refine ⟨73008247600041265392789757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97344330133388353857053009 73008247600041265392789757)
      ·
        refine ⟨27378092850015474522296159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73008247600041265392789757 27378092850015474522296159)
        ·
          refine ⟨41067139275023211783444239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27378092850015474522296159 41067139275023211783444239)
          ·
            refine ⟨61600708912534817675166359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41067139275023211783444239 61600708912534817675166359)
            ·
              refine ⟨92401063368802226512749539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61600708912534817675166359 92401063368802226512749539)
              ·
                refine ⟨138601595053203339769124309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92401063368802226512749539 138601595053203339769124309)
                ·
                  refine ⟨3248474884059453275838851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 138601595053203339769124309 3248474884059453275838851)
                  ·
                    refine ⟨4872712326089179913758277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3248474884059453275838851 4872712326089179913758277)
                    ·
                      refine ⟨913633561141721233829677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4872712326089179913758277 913633561141721233829677)
                      ·
                        rfl

theorem cell23_1779295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 7, 1, 4].length) (baseStart_1779295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1779295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1779295 prefixEnd_1779295 := by exact prefixLift 1779295
  have htrace : WordTrace (prefixWord ++ tailWord_1779295) baseStart_1779295 baseEnd_1779295 := by
    simpa [prefixWord, tailWord_1779295, baseEnd_1779295] using wordTrace_append hprefix tailTrace_1779295
  have hstable : (prefixWord ++ tailWord_1779295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779295).length < 2 ^ (prefixWord ++ tailWord_1779295).sum := by decide
  have hdescent : baseEnd_1779295 < baseStart_1779295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779299 : List Nat := [1, 1, 1, 5, 1, 4, 1, 2, 2, 3, 2]
def baseStart_1779299 : Nat := 118140960795 + 1779299 * 2 ^ 59
def prefixEnd_1779299 : Nat := 4983230072969 + 3 ^ 40 * 1779299 * 2
def baseEnd_1779299 : Nat := 913635615064339218179659

theorem tailTrace_1779299 : CollatzResearch.WordTrace tailWord_1779299 prefixEnd_1779299 913635615064339218179659 := by
  unfold tailWord_1779299
  simp only [CollatzResearch.WordTrace]
  refine ⟨64896365980911077921180951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43264243987274051947453967 64896365980911077921180951)
  ·
    refine ⟨97344548971366616881771427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64896365980911077921180951 97344548971366616881771427)
    ·
      refine ⟨146016823457049925322657141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97344548971366616881771427 146016823457049925322657141)
      ·
        refine ⟨13689077199098430498999107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 146016823457049925322657141 13689077199098430498999107)
        ·
          refine ⟨20533615798647645748498661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13689077199098430498999107 20533615798647645748498661)
          ·
            refine ⟨3850052962246433577843499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20533615798647645748498661 3850052962246433577843499)
            ·
              refine ⟨5775079443369650366765249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3850052962246433577843499 5775079443369650366765249)
              ·
                refine ⟨4331309582527237775073937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5775079443369650366765249 4331309582527237775073937)
                ·
                  refine ⟨3248482186895428331305453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4331309582527237775073937 3248482186895428331305453)
                  ·
                    refine ⟨1218180820085785624239545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3248482186895428331305453 1218180820085785624239545)
                    ·
                      refine ⟨913635615064339218179659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1218180820085785624239545 913635615064339218179659)
                      ·
                        rfl

theorem cell23_1779299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 2, 2, 3, 2].length) (baseStart_1779299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1779299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1779299 prefixEnd_1779299 := by exact prefixLift 1779299
  have htrace : WordTrace (prefixWord ++ tailWord_1779299) baseStart_1779299 baseEnd_1779299 := by
    simpa [prefixWord, tailWord_1779299, baseEnd_1779299] using wordTrace_append hprefix tailTrace_1779299
  have hstable : (prefixWord ++ tailWord_1779299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779299).length < 2 ^ (prefixWord ++ tailWord_1779299).sum := by decide
  have hdescent : baseEnd_1779299 < baseStart_1779299 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779306 : List Nat := [3, 1, 3, 2, 1, 4, 1, 1, 3, 1, 3]
def baseStart_1779306 : Nat := 118140960795 + 1779306 * 2 ^ 59
def prefixEnd_1779306 : Nat := 4983230072969 + 3 ^ 40 * 1779306 * 2
def baseEnd_1779306 : Nat := 913639209428920690792127

theorem tailTrace_1779306 : CollatzResearch.WordTrace tailWord_1779306 prefixEnd_1779306 913639209428920690792127 := by
  unfold tailWord_1779306
  simp only [CollatzResearch.WordTrace]
  refine ⟨16224155322971429529171443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43264414194590478744457181 16224155322971429529171443)
  ·
    refine ⟨24336232984457144293757165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16224155322971429529171443 24336232984457144293757165)
    ·
      refine ⟨9126087369171429110158937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24336232984457144293757165 9126087369171429110158937)
      ·
        refine ⟨6844565526878571832619203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9126087369171429110158937 6844565526878571832619203)
        ·
          refine ⟨10266848290317857748928805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6844565526878571832619203 10266848290317857748928805)
          ·
            refine ⟨1925034054434598327924151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10266848290317857748928805 1925034054434598327924151)
            ·
              refine ⟨2887551081651897491886227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1925034054434598327924151 2887551081651897491886227)
              ·
                refine ⟨4331326622477846237829341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2887551081651897491886227 4331326622477846237829341)
                ·
                  refine ⟨1624247483429192339186003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4331326622477846237829341 1624247483429192339186003)
                  ·
                    refine ⟨2436371225143788508779005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1624247483429192339186003 2436371225143788508779005)
                    ·
                      refine ⟨913639209428920690792127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2436371225143788508779005 913639209428920690792127)
                      ·
                        rfl

theorem cell23_1779306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_1779306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1779306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1779306 prefixEnd_1779306 := by exact prefixLift 1779306
  have htrace : WordTrace (prefixWord ++ tailWord_1779306) baseStart_1779306 baseEnd_1779306 := by
    simpa [prefixWord, tailWord_1779306, baseEnd_1779306] using wordTrace_append hprefix tailTrace_1779306
  have hstable : (prefixWord ++ tailWord_1779306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779306).length < 2 ^ (prefixWord ++ tailWord_1779306).sum := by decide
  have hdescent : baseEnd_1779306 < baseStart_1779306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779329 : List Nat := [1, 2, 4, 2, 1, 2, 3, 2, 1, 1, 4]
def baseStart_1779329 : Nat := 118140960795 + 1779329 * 2 ^ 59
def prefixEnd_1779329 : Nat := 4983230072969 + 3 ^ 40 * 1779329 * 2
def baseEnd_1779329 : Nat := 913651019483974100804521

theorem tailTrace_1779329 : CollatzResearch.WordTrace tailWord_1779329 prefixEnd_1779329 913651019483974100804521 := by
  unfold tailWord_1779329
  simp only [CollatzResearch.WordTrace]
  refine ⟨64897460170802393044773041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43264973447201595363182027 64897460170802393044773041)
  ·
    refine ⟨48673095128101794783579781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64897460170802393044773041 48673095128101794783579781)
    ·
      refine ⟨9126205336519086521921209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48673095128101794783579781 9126205336519086521921209)
      ·
        refine ⟨6844654002389314891440907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9126205336519086521921209 6844654002389314891440907)
        ·
          refine ⟨10266981003583972337161361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6844654002389314891440907 10266981003583972337161361)
          ·
            refine ⟨7700235752687979252871021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10266981003583972337161361 7700235752687979252871021)
            ·
              refine ⟨2887588407257992219826633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7700235752687979252871021 2887588407257992219826633)
              ·
                refine ⟨2165691305443494164869975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2887588407257992219826633 2165691305443494164869975)
                ·
                  refine ⟨3248536958165241247304963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2165691305443494164869975 3248536958165241247304963)
                  ·
                    refine ⟨4872805437247861870957445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3248536958165241247304963 4872805437247861870957445)
                    ·
                      refine ⟨913651019483974100804521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4872805437247861870957445 913651019483974100804521)
                      ·
                        rfl

theorem cell23_1779329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_1779329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1779329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1779329 prefixEnd_1779329 := by exact prefixLift 1779329
  have htrace : WordTrace (prefixWord ++ tailWord_1779329) baseStart_1779329 baseEnd_1779329 := by
    simpa [prefixWord, tailWord_1779329, baseEnd_1779329] using wordTrace_append hprefix tailTrace_1779329
  have hstable : (prefixWord ++ tailWord_1779329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779329).length < 2 ^ (prefixWord ++ tailWord_1779329).sum := by decide
  have hdescent : baseEnd_1779329 < baseStart_1779329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779335 : List Nat := [1, 1, 4, 2, 1, 3, 2, 9]
def baseStart_1779335 : Nat := 118140960795 + 1779335 * 2 ^ 59
def prefixEnd_1779335 : Nat := 4983230072969 + 3 ^ 40 * 1779335 * 2
def baseEnd_1779335 : Nat := 33839040754366706567759

theorem tailTrace_1779335 : CollatzResearch.WordTrace tailWord_1779335 prefixEnd_1779335 33839040754366706567759 := by
  unfold tailWord_1779335
  simp only [CollatzResearch.WordTrace]
  refine ⟨64897679008780656069491459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43265119339187104046327639 64897679008780656069491459)
  ·
    refine ⟨97346518513170984104237189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64897679008780656069491459 97346518513170984104237189)
    ·
      refine ⟨18252472221219559519544473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97346518513170984104237189 18252472221219559519544473)
      ·
        refine ⟨13689354165914669639658355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18252472221219559519544473 13689354165914669639658355)
        ·
          refine ⟨20534031248872004459487533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13689354165914669639658355 20534031248872004459487533)
          ·
            refine ⟨7700261718327001672307825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20534031248872004459487533 7700261718327001672307825)
            ·
              refine ⟨5775196288745251254230869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7700261718327001672307825 5775196288745251254230869)
              ·
                refine ⟨33839040754366706567759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5775196288745251254230869 33839040754366706567759)
                ·
                  rfl

theorem cell23_1779335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 9].length) (baseStart_1779335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1779335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1779335 prefixEnd_1779335 := by exact prefixLift 1779335
  have htrace : WordTrace (prefixWord ++ tailWord_1779335) baseStart_1779335 baseEnd_1779335 := by
    simpa [prefixWord, tailWord_1779335, baseEnd_1779335] using wordTrace_append hprefix tailTrace_1779335
  have hstable : (prefixWord ++ tailWord_1779335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779335).length < 2 ^ (prefixWord ++ tailWord_1779335).sum := by decide
  have hdescent : baseEnd_1779335 < baseStart_1779335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779342 : List Nat := [4, 1, 1, 3, 1, 2, 1, 1, 3, 2, 4]
def baseStart_1779342 : Nat := 118140960795 + 1779342 * 2 ^ 59
def prefixEnd_1779342 : Nat := 4983230072969 + 3 ^ 40 * 1779342 * 2
def baseEnd_1779342 : Nat := 913657694732482549941961

theorem tailTrace_1779342 : CollatzResearch.WordTrace tailWord_1779342 prefixEnd_1779342 913657694732482549941961 := by
  unfold tailWord_1779342
  simp only [CollatzResearch.WordTrace]
  refine ⟨8112241789969412033124535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43265289546503530843330853 8112241789969412033124535)
  ·
    refine ⟨12168362684954118049686803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8112241789969412033124535 12168362684954118049686803)
    ·
      refine ⟨18252544027431177074530205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12168362684954118049686803 18252544027431177074530205)
      ·
        refine ⟨6844704010286691402948827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18252544027431177074530205 6844704010286691402948827)
        ·
          refine ⟨10267056015430037104423241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6844704010286691402948827 10267056015430037104423241)
          ·
            refine ⟨7700292011572527828317431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10267056015430037104423241 7700292011572527828317431)
            ·
              refine ⟨11550438017358791742476147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7700292011572527828317431 11550438017358791742476147)
              ·
                refine ⟨17325657026038187613714221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11550438017358791742476147 17325657026038187613714221)
                ·
                  refine ⟨6497121384764320355142833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17325657026038187613714221 6497121384764320355142833)
                  ·
                    refine ⟨4872841038573240266357125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6497121384764320355142833 4872841038573240266357125)
                    ·
                      refine ⟨913657694732482549941961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4872841038573240266357125 913657694732482549941961)
                      ·
                        rfl

theorem cell23_1779342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_1779342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1779342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1779342 prefixEnd_1779342 := by exact prefixLift 1779342
  have htrace : WordTrace (prefixWord ++ tailWord_1779342) baseStart_1779342 baseEnd_1779342 := by
    simpa [prefixWord, tailWord_1779342, baseEnd_1779342] using wordTrace_append hprefix tailTrace_1779342
  have hstable : (prefixWord ++ tailWord_1779342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779342).length < 2 ^ (prefixWord ++ tailWord_1779342).sum := by decide
  have hdescent : baseEnd_1779342 < baseStart_1779342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779356 : List Nat := [2, 2, 3, 2, 3, 1, 2, 2, 2, 4]
def baseStart_1779356 : Nat := 118140960795 + 1779356 * 2 ^ 59
def prefixEnd_1779356 : Nat := 4983230072969 + 3 ^ 40 * 1779356 * 2
def baseEnd_1779356 : Nat := 304554961153881831722299

theorem tailTrace_1779356 : CollatzResearch.WordTrace tailWord_1779356 prefixEnd_1779356 304554961153881831722299 := by
  unfold tailWord_1779356
  simp only [CollatzResearch.WordTrace]
  refine ⟨32449222470852288328002961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43265629961136384437337281 32449222470852288328002961)
  ·
    refine ⟨24336916853139216246002221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32449222470852288328002961 24336916853139216246002221)
    ·
      refine ⟨9126343819927206092250833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24336916853139216246002221 9126343819927206092250833)
      ·
        refine ⟨6844757864945404569188125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9126343819927206092250833 6844757864945404569188125)
        ·
          refine ⟨2566784199354526713445547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6844757864945404569188125 2566784199354526713445547)
          ·
            refine ⟨3850176299031790070168321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2566784199354526713445547 3850176299031790070168321)
            ·
              refine ⟨2887632224273842552626241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3850176299031790070168321 2887632224273842552626241)
              ·
                refine ⟨2165724168205381914469681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2887632224273842552626241 2165724168205381914469681)
                ·
                  refine ⟨1624293126154036435852261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2165724168205381914469681 1624293126154036435852261)
                  ·
                    refine ⟨304554961153881831722299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1624293126154036435852261 304554961153881831722299)
                    ·
                      rfl

theorem cell23_1779356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_1779356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1779356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1779356 prefixEnd_1779356 := by exact prefixLift 1779356
  have htrace : WordTrace (prefixWord ++ tailWord_1779356) baseStart_1779356 baseEnd_1779356 := by
    simpa [prefixWord, tailWord_1779356, baseEnd_1779356] using wordTrace_append hprefix tailTrace_1779356
  have hstable : (prefixWord ++ tailWord_1779356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779356).length < 2 ^ (prefixWord ++ tailWord_1779356).sum := by decide
  have hdescent : baseEnd_1779356 < baseStart_1779356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779365 : List Nat := [1, 3, 1, 2, 1, 2, 3, 1, 2, 7]
def baseStart_1779365 : Nat := 118140960795 + 1779365 * 2 ^ 59
def prefixEnd_1779365 : Nat := 4983230072969 + 3 ^ 40 * 1779365 * 2
def baseEnd_1779365 : Nat := 304556501595845319984785

theorem tailTrace_1779365 : CollatzResearch.WordTrace tailWord_1779365 prefixEnd_1779365 304556501595845319984785 := by
  unfold tailWord_1779365
  simp only [CollatzResearch.WordTrace]
  refine ⟨64898773198671971193083549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43265848799114647462055699 64898773198671971193083549)
  ·
    refine ⟨24337039949501989197406331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64898773198671971193083549 24337039949501989197406331)
    ·
      refine ⟨36505559924252983796109497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24337039949501989197406331 36505559924252983796109497)
      ·
        refine ⟨27379169943189737847082123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36505559924252983796109497 27379169943189737847082123)
        ·
          refine ⟨41068754914784606770623185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27379169943189737847082123 41068754914784606770623185)
          ·
            refine ⟨30801566186088455077967389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41068754914784606770623185 30801566186088455077967389)
            ·
              refine ⟨11550587319783170654237771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30801566186088455077967389 11550587319783170654237771)
              ·
                refine ⟨17325880979674755981356657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11550587319783170654237771 17325880979674755981356657)
                ·
                  refine ⟨12994410734756066986017493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17325880979674755981356657 12994410734756066986017493)
                  ·
                    refine ⟨304556501595845319984785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12994410734756066986017493 304556501595845319984785)
                    ·
                      rfl

theorem cell23_1779365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 7].length) (baseStart_1779365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1779365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1779365 prefixEnd_1779365 := by exact prefixLift 1779365
  have htrace : WordTrace (prefixWord ++ tailWord_1779365) baseStart_1779365 baseEnd_1779365 := by
    simpa [prefixWord, tailWord_1779365, baseEnd_1779365] using wordTrace_append hprefix tailTrace_1779365
  have hstable : (prefixWord ++ tailWord_1779365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779365).length < 2 ^ (prefixWord ++ tailWord_1779365).sum := by decide
  have hdescent : baseEnd_1779365 < baseStart_1779365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779379 : List Nat := [1, 1, 1, 2, 3, 3, 1, 5, 2, 1, 3]
def baseStart_1779379 : Nat := 118140960795 + 1779379 * 2 ^ 59
def prefixEnd_1779379 : Nat := 4983230072969 + 3 ^ 40 * 1779379 * 2
def baseEnd_1779379 : Nat := 913676693516698905179291

theorem tailTrace_1779379 : CollatzResearch.WordTrace tailWord_1779379 prefixEnd_1779379 913676693516698905179291 := by
  unfold tailWord_1779379
  simp only [CollatzResearch.WordTrace]
  refine ⟨64899283820621251584093191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43266189213747501056062127 64899283820621251584093191)
  ·
    refine ⟨97348925730931877376139787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64899283820621251584093191 97348925730931877376139787)
    ·
      refine ⟨146023388596397816064209681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97348925730931877376139787 146023388596397816064209681)
      ·
        refine ⟨109517541447298362048157261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146023388596397816064209681 109517541447298362048157261)
        ·
          refine ⟨41069078042736885768058973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109517541447298362048157261 41069078042736885768058973)
          ·
            refine ⟨15400904266026332163022115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41069078042736885768058973 15400904266026332163022115)
            ·
              refine ⟨23101356399039498244533173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15400904266026332163022115 23101356399039498244533173)
              ·
                refine ⟨2165752162409952960424985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23101356399039498244533173 2165752162409952960424985)
                ·
                  refine ⟨1624314121807464720318739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2165752162409952960424985 1624314121807464720318739)
                  ·
                    refine ⟨2436471182711197080478109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1624314121807464720318739 2436471182711197080478109)
                    ·
                      refine ⟨913676693516698905179291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2436471182711197080478109 913676693516698905179291)
                      ·
                        rfl

theorem cell23_1779379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 5, 2, 1, 3].length) (baseStart_1779379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1779379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1779379 prefixEnd_1779379 := by exact prefixLift 1779379
  have htrace : WordTrace (prefixWord ++ tailWord_1779379) baseStart_1779379 baseEnd_1779379 := by
    simpa [prefixWord, tailWord_1779379, baseEnd_1779379] using wordTrace_append hprefix tailTrace_1779379
  have hstable : (prefixWord ++ tailWord_1779379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779379).length < 2 ^ (prefixWord ++ tailWord_1779379).sum := by decide
  have hdescent : baseEnd_1779379 < baseStart_1779379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779389 : List Nat := [1, 4, 1, 2, 1, 2, 1, 3, 3, 3, 2]
def baseStart_1779389 : Nat := 118140960795 + 1779389 * 2 ^ 59
def prefixEnd_1779389 : Nat := 4983230072969 + 3 ^ 40 * 1779389 * 2
def baseEnd_1779389 : Nat := 913681828323243866054245

theorem tailTrace_1779389 : CollatzResearch.WordTrace tailWord_1779389 prefixEnd_1779389 913681828323243866054245 := by
  unfold tailWord_1779389
  simp only [CollatzResearch.WordTrace]
  refine ⟨64899648550585023291957221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43266432367056682194638147 64899648550585023291957221)
  ·
    refine ⟨12168684103234691867241979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64899648550585023291957221 12168684103234691867241979)
    ·
      refine ⟨18253026154852037800862969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12168684103234691867241979 18253026154852037800862969)
      ·
        refine ⟨13689769616139028350647227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18253026154852037800862969 13689769616139028350647227)
        ·
          refine ⟨20534654424208542525970841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13689769616139028350647227 20534654424208542525970841)
          ·
            refine ⟨15400990818156406894478131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20534654424208542525970841 15400990818156406894478131)
            ·
              refine ⟨23101486227234610341717197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15400990818156406894478131 23101486227234610341717197)
              ·
                refine ⟨8663057335212978878143949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23101486227234610341717197 8663057335212978878143949)
                ·
                  refine ⟨3248646500704867079303981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8663057335212978878143949 3248646500704867079303981)
                  ·
                    refine ⟨1218242437764325154738993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3248646500704867079303981 1218242437764325154738993)
                    ·
                      refine ⟨913681828323243866054245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1218242437764325154738993 913681828323243866054245)
                      ·
                        rfl

theorem cell23_1779389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 3, 3, 2].length) (baseStart_1779389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1779389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1779389 prefixEnd_1779389 := by exact prefixLift 1779389
  have htrace : WordTrace (prefixWord ++ tailWord_1779389) baseStart_1779389 baseEnd_1779389 := by
    simpa [prefixWord, tailWord_1779389, baseEnd_1779389] using wordTrace_append hprefix tailTrace_1779389
  have hstable : (prefixWord ++ tailWord_1779389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779389).length < 2 ^ (prefixWord ++ tailWord_1779389).sum := by decide
  have hdescent : baseEnd_1779389 < baseStart_1779389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779406 : List Nat := [4, 1, 1, 1, 3, 1, 3, 3, 1, 3, 2]
def baseStart_1779406 : Nat := 118140960795 + 1779406 * 2 ^ 59
def prefixEnd_1779406 : Nat := 4983230072969 + 3 ^ 40 * 1779406 * 2
def baseEnd_1779406 : Nat := 913690557494370299541667

theorem tailTrace_1779406 : CollatzResearch.WordTrace tailWord_1779406 prefixEnd_1779406 913690557494370299541667 := by
  unfold tailWord_1779406
  simp only [CollatzResearch.WordTrace]
  refine ⟨8112533573940429399415759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43266845727682290130217381 8112533573940429399415759)
  ·
    refine ⟨12168800360910644099123639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8112533573940429399415759 12168800360910644099123639)
    ·
      refine ⟨18253200541365966148685459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12168800360910644099123639 18253200541365966148685459)
      ·
        refine ⟨27379800812048949223028189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18253200541365966148685459 27379800812048949223028189)
        ·
          refine ⟨10267425304518355958635571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27379800812048949223028189 10267425304518355958635571)
          ·
            refine ⟨15401137956777533937953357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10267425304518355958635571 15401137956777533937953357)
            ·
              refine ⟨5775426733791575226732509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15401137956777533937953357 5775426733791575226732509)
              ·
                refine ⟨2165785025171840710024691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5775426733791575226732509 2165785025171840710024691)
                ·
                  refine ⟨3248677537757761065037037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2165785025171840710024691 3248677537757761065037037)
                  ·
                    refine ⟨1218254076659160399388889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3248677537757761065037037 1218254076659160399388889)
                    ·
                      refine ⟨913690557494370299541667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1218254076659160399388889 913690557494370299541667)
                      ·
                        rfl

theorem cell23_1779406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 3, 1, 3, 2].length) (baseStart_1779406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1779406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1779406 prefixEnd_1779406 := by exact prefixLift 1779406
  have htrace : WordTrace (prefixWord ++ tailWord_1779406) baseStart_1779406 baseEnd_1779406 := by
    simpa [prefixWord, tailWord_1779406, baseEnd_1779406] using wordTrace_append hprefix tailTrace_1779406
  have hstable : (prefixWord ++ tailWord_1779406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779406).length < 2 ^ (prefixWord ++ tailWord_1779406).sum := by decide
  have hdescent : baseEnd_1779406 < baseStart_1779406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779436 : List Nat := [2, 2, 1, 1, 2, 2, 2, 5, 2, 2, 2]
def baseStart_1779436 : Nat := 118140960795 + 1779436 * 2 ^ 59
def prefixEnd_1779436 : Nat := 4983230072969 + 3 ^ 40 * 1779436 * 2
def baseEnd_1779436 : Nat := 913705961914005182166529

theorem tailTrace_1779436 : CollatzResearch.WordTrace tailWord_1779436 prefixEnd_1779436 913705961914005182166529 := by
  unfold tailWord_1779436
  simp only [CollatzResearch.WordTrace]
  refine ⟨32450681390707375159459081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43267575187609833545945441 32450681390707375159459081)
  ·
    refine ⟨24338011043030531369594311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32450681390707375159459081 24338011043030531369594311)
    ·
      refine ⟨36507016564545797054391467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24338011043030531369594311 36507016564545797054391467)
      ·
        refine ⟨54760524846818695581587201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36507016564545797054391467 54760524846818695581587201)
        ·
          refine ⟨41070393635114021686190401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54760524846818695581587201 41070393635114021686190401)
          ·
            refine ⟨30802795226335516264642801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41070393635114021686190401 30802795226335516264642801)
            ·
              refine ⟨23102096419751637198482101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30802795226335516264642801 23102096419751637198482101)
              ·
                refine ⟨2165821539351715987357697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23102096419751637198482101 2165821539351715987357697)
                ·
                  refine ⟨1624366154513786990518273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2165821539351715987357697 1624366154513786990518273)
                  ·
                    refine ⟨1218274615885340242888705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1624366154513786990518273 1218274615885340242888705)
                    ·
                      refine ⟨913705961914005182166529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1218274615885340242888705 913705961914005182166529)
                      ·
                        rfl

theorem cell23_1779436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 2, 2].length) (baseStart_1779436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1779436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1779436 prefixEnd_1779436 := by exact prefixLift 1779436
  have htrace : WordTrace (prefixWord ++ tailWord_1779436) baseStart_1779436 baseEnd_1779436 := by
    simpa [prefixWord, tailWord_1779436, baseEnd_1779436] using wordTrace_append hprefix tailTrace_1779436
  have hstable : (prefixWord ++ tailWord_1779436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779436).length < 2 ^ (prefixWord ++ tailWord_1779436).sum := by decide
  have hdescent : baseEnd_1779436 < baseStart_1779436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779442 : List Nat := [3, 2, 1, 3, 1, 1, 1, 4, 7]
def baseStart_1779442 : Nat := 118140960795 + 1779442 * 2 ^ 59
def prefixEnd_1779442 : Nat := 4983230072969 + 3 ^ 40 * 1779442 * 2
def baseEnd_1779442 : Nat := 101523226977548017632389

theorem tailTrace_1779442 : CollatzResearch.WordTrace tailWord_1779442 prefixEnd_1779442 101523226977548017632389 := by
  unfold tailWord_1779442
  simp only [CollatzResearch.WordTrace]
  refine ⟨16225395404848253335909145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43267721079595342229091053 16225395404848253335909145)
  ·
    refine ⟨12169046553636190001931859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16225395404848253335909145 12169046553636190001931859)
    ·
      refine ⟨18253569830454285002897789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12169046553636190001931859 18253569830454285002897789)
      ·
        refine ⟨6845088686420356876086671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18253569830454285002897789 6845088686420356876086671)
        ·
          refine ⟨10267633029630535314130007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6845088686420356876086671 10267633029630535314130007)
          ·
            refine ⟨15401449544445802971195011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10267633029630535314130007 15401449544445802971195011)
            ·
              refine ⟨23102174316668704456792517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15401449544445802971195011 23102174316668704456792517)
              ·
                refine ⟨4331657684375382085648597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23102174316668704456792517 4331657684375382085648597)
                ·
                  refine ⟨101523226977548017632389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4331657684375382085648597 101523226977548017632389)
                  ·
                    rfl

theorem cell23_1779442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4, 7].length) (baseStart_1779442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1779442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1779442 prefixEnd_1779442 := by exact prefixLift 1779442
  have htrace : WordTrace (prefixWord ++ tailWord_1779442) baseStart_1779442 baseEnd_1779442 := by
    simpa [prefixWord, tailWord_1779442, baseEnd_1779442] using wordTrace_append hprefix tailTrace_1779442
  have hstable : (prefixWord ++ tailWord_1779442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779442).length < 2 ^ (prefixWord ++ tailWord_1779442).sum := by decide
  have hdescent : baseEnd_1779442 < baseStart_1779442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779459 : List Nat := [1, 1, 1, 3, 2, 2, 5, 3, 5]
def baseStart_1779459 : Nat := 118140960795 + 1779459 * 2 ^ 59
def prefixEnd_1779459 : Nat := 4983230072969 + 3 ^ 40 * 1779459 * 2
def baseEnd_1779459 : Nat := 101524196885450954686547

theorem tailTrace_1779459 : CollatzResearch.WordTrace tailWord_1779459 prefixEnd_1779459 101524196885450954686547 := by
  unfold tailWord_1779459
  simp only [CollatzResearch.WordTrace]
  refine ⟨64902201660331425247005431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43268134440220950164670287 64902201660331425247005431)
  ·
    refine ⟨97353302490497137870508147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64902201660331425247005431 97353302490497137870508147)
    ·
      refine ⟨146029953735745706805762221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97353302490497137870508147 146029953735745706805762221)
      ·
        refine ⟨54761232650904640052160833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146029953735745706805762221 54761232650904640052160833)
        ·
          refine ⟨41070924488178480039120625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54761232650904640052160833 41070924488178480039120625)
          ·
            refine ⟨30803193366133860029340469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41070924488178480039120625 30803193366133860029340469)
            ·
              refine ⟨2887799378075049377750669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30803193366133860029340469 2887799378075049377750669)
              ·
                refine ⟨1082924766778143516656501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2887799378075049377750669 1082924766778143516656501)
                ·
                  refine ⟨101524196885450954686547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1082924766778143516656501 101524196885450954686547)
                  ·
                    rfl

theorem cell23_1779459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 3, 5].length) (baseStart_1779459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1779459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1779459 prefixEnd_1779459 := by exact prefixLift 1779459
  have htrace : WordTrace (prefixWord ++ tailWord_1779459) baseStart_1779459 baseEnd_1779459 := by
    simpa [prefixWord, tailWord_1779459, baseEnd_1779459] using wordTrace_append hprefix tailTrace_1779459
  have hstable : (prefixWord ++ tailWord_1779459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779459).length < 2 ^ (prefixWord ++ tailWord_1779459).sum := by decide
  have hdescent : baseEnd_1779459 < baseStart_1779459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779482 : List Nat := [3, 1, 1, 3, 2, 2, 1, 1, 1, 1, 7]
def baseStart_1779482 : Nat := 118140960795 + 1779482 * 2 ^ 59
def prefixEnd_1779482 : Nat := 4983230072969 + 3 ^ 40 * 1779482 * 2
def baseEnd_1779482 : Nat := 913729582024112002191317

theorem tailTrace_1779482 : CollatzResearch.WordTrace tailWord_1779482 prefixEnd_1779482 913729582024112002191317 := by
  unfold tailWord_1779482
  simp only [CollatzResearch.WordTrace]
  refine ⟨16225760134812025043773175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43268693692832066783395133 16225760134812025043773175)
  ·
    refine ⟨24338640202218037565659763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16225760134812025043773175 24338640202218037565659763)
    ·
      refine ⟨36507960303327056348489645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24338640202218037565659763 36507960303327056348489645)
      ·
        refine ⟨13690485113747646130683617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36507960303327056348489645 13690485113747646130683617)
        ·
          refine ⟨10267863835310734598012713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13690485113747646130683617 10267863835310734598012713)
          ·
            refine ⟨7700897876483050948509535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10267863835310734598012713 7700897876483050948509535)
            ·
              refine ⟨11551346814724576422764303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7700897876483050948509535 11551346814724576422764303)
              ·
                refine ⟨17327020222086864634146455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11551346814724576422764303 17327020222086864634146455)
                ·
                  refine ⟨25990530333130296951219683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17327020222086864634146455 25990530333130296951219683)
                  ·
                    refine ⟨38985795499695445426829525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25990530333130296951219683 38985795499695445426829525)
                    ·
                      refine ⟨913729582024112002191317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 38985795499695445426829525 913729582024112002191317)
                      ·
                        rfl

theorem cell23_1779482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_1779482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1779482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1779482 prefixEnd_1779482 := by exact prefixLift 1779482
  have htrace : WordTrace (prefixWord ++ tailWord_1779482) baseStart_1779482 baseEnd_1779482 := by
    simpa [prefixWord, tailWord_1779482, baseEnd_1779482] using wordTrace_append hprefix tailTrace_1779482
  have hstable : (prefixWord ++ tailWord_1779482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779482).length < 2 ^ (prefixWord ++ tailWord_1779482).sum := by decide
  have hdescent : baseEnd_1779482 < baseStart_1779482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779529 : List Nat := [1, 2, 1, 1, 2, 4, 1, 4, 2, 2, 3]
def baseStart_1779529 : Nat := 118140960795 + 1779529 * 2 ^ 59
def prefixEnd_1779529 : Nat := 4983230072969 + 3 ^ 40 * 1779529 * 2
def baseEnd_1779529 : Nat := 913753715614873318303601

theorem tailTrace_1779529 : CollatzResearch.WordTrace tailWord_1779529 prefixEnd_1779529 913753715614873318303601 := by
  unfold tailWord_1779529
  simp only [CollatzResearch.WordTrace]
  refine ⟨64904754770077827202053641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43269836513385218134702427 64904754770077827202053641)
  ·
    refine ⟨48678566077558370401540231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64904754770077827202053641 48678566077558370401540231)
    ·
      refine ⟨73017849116337555602310347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48678566077558370401540231 73017849116337555602310347)
      ·
        refine ⟨109526773674506333403465521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73017849116337555602310347 109526773674506333403465521)
        ·
          refine ⟨82145080255879750052599141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109526773674506333403465521 82145080255879750052599141)
          ·
            refine ⟨15402202547977453134862339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82145080255879750052599141 15402202547977453134862339)
            ·
              refine ⟨23103303821966179702293509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15402202547977453134862339 23103303821966179702293509)
              ·
                refine ⟨4331869466618658694180033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23103303821966179702293509 4331869466618658694180033)
                ·
                  refine ⟨3248902099963994020635025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4331869466618658694180033 3248902099963994020635025)
                  ·
                    refine ⟨2436676574972995515476269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3248902099963994020635025 2436676574972995515476269)
                    ·
                      refine ⟨913753715614873318303601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2436676574972995515476269 913753715614873318303601)
                      ·
                        rfl

theorem cell23_1779529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4, 2, 2, 3].length) (baseStart_1779529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1779529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1779529 prefixEnd_1779529 := by exact prefixLift 1779529
  have htrace : WordTrace (prefixWord ++ tailWord_1779529) baseStart_1779529 baseEnd_1779529 := by
    simpa [prefixWord, tailWord_1779529, baseEnd_1779529] using wordTrace_append hprefix tailTrace_1779529
  have hstable : (prefixWord ++ tailWord_1779529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779529).length < 2 ^ (prefixWord ++ tailWord_1779529).sum := by decide
  have hdescent : baseEnd_1779529 < baseStart_1779529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779593 : List Nat := [1, 2, 1, 1, 5, 1, 1, 6, 1, 1, 3]
def baseStart_1779593 : Nat := 118140960795 + 1779593 * 2 ^ 59
def prefixEnd_1779593 : Nat := 4983230072969 + 3 ^ 40 * 1779593 * 2
def baseEnd_1779593 : Nat := 913786578376761067903307

theorem tailTrace_1779593 : CollatzResearch.WordTrace tailWord_1779593 prefixEnd_1779593 913786578376761067903307 := by
  unfold tailWord_1779593
  simp only [CollatzResearch.WordTrace]
  refine ⟨64907089041845966132383433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43271392694563977421588955 64907089041845966132383433)
  ·
    refine ⟨48680316781384474599287575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64907089041845966132383433 48680316781384474599287575)
    ·
      refine ⟨73020475172076711898931363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48680316781384474599287575 73020475172076711898931363)
      ·
        refine ⟨109530712758115067848397045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73020475172076711898931363 109530712758115067848397045)
        ·
          refine ⟨10268504321073287610787223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 109530712758115067848397045 10268504321073287610787223)
          ·
            refine ⟨15402756481609931416180835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10268504321073287610787223 15402756481609931416180835)
            ·
              refine ⟨23104134722414897124271253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15402756481609931416180835 23104134722414897124271253)
              ·
                refine ⟨1083006315113198302700215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23104134722414897124271253 1083006315113198302700215)
                ·
                  refine ⟨1624509472669797454050323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1083006315113198302700215 1624509472669797454050323)
                  ·
                    refine ⟨2436764209004696181075485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1624509472669797454050323 2436764209004696181075485)
                    ·
                      refine ⟨913786578376761067903307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2436764209004696181075485 913786578376761067903307)
                      ·
                        rfl

theorem cell23_1779593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 6, 1, 1, 3].length) (baseStart_1779593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1779593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1779593 prefixEnd_1779593 := by exact prefixLift 1779593
  have htrace : WordTrace (prefixWord ++ tailWord_1779593) baseStart_1779593 baseEnd_1779593 := by
    simpa [prefixWord, tailWord_1779593, baseEnd_1779593] using wordTrace_append hprefix tailTrace_1779593
  have hstable : (prefixWord ++ tailWord_1779593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779593).length < 2 ^ (prefixWord ++ tailWord_1779593).sum := by decide
  have hdescent : baseEnd_1779593 < baseStart_1779593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779609 : List Nat := [1, 2, 1, 2, 1, 3, 5, 1, 1, 6]
def baseStart_1779609 : Nat := 118140960795 + 1779609 * 2 ^ 59
def prefixEnd_1779609 : Nat := 4983230072969 + 3 ^ 40 * 1779609 * 2
def baseEnd_1779609 : Nat := 304598264689077668434411

theorem tailTrace_1779609 : CollatzResearch.WordTrace tailWord_1779609 prefixEnd_1779609 304598264689077668434411 := by
  unfold tailWord_1779609
  simp only [CollatzResearch.WordTrace]
  refine ⟨64907672609788000864965881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43271781739858667243310587 64907672609788000864965881)
  ·
    refine ⟨48680754457341000648724411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64907672609788000864965881 48680754457341000648724411)
    ·
      refine ⟨73021131686011500973086617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48680754457341000648724411 73021131686011500973086617)
      ·
        refine ⟨54765848764508625729814963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73021131686011500973086617 54765848764508625729814963)
        ·
          refine ⟨82148773146762938594722445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54765848764508625729814963 82148773146762938594722445)
          ·
            refine ⟨30805789930036101973020917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82148773146762938594722445 30805789930036101973020917)
            ·
              refine ⟨2888042805940884559970711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30805789930036101973020917 2888042805940884559970711)
              ·
                refine ⟨4332064208911326839956067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2888042805940884559970711 4332064208911326839956067)
                ·
                  refine ⟨6498096313366990259934101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4332064208911326839956067 6498096313366990259934101)
                  ·
                    refine ⟨304598264689077668434411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6498096313366990259934101 304598264689077668434411)
                    ·
                      rfl

theorem cell23_1779609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 1, 1, 6].length) (baseStart_1779609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1779609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1779609 prefixEnd_1779609 := by exact prefixLift 1779609
  have htrace : WordTrace (prefixWord ++ tailWord_1779609) baseStart_1779609 baseEnd_1779609 := by
    simpa [prefixWord, tailWord_1779609, baseEnd_1779609] using wordTrace_append hprefix tailTrace_1779609
  have hstable : (prefixWord ++ tailWord_1779609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779609).length < 2 ^ (prefixWord ++ tailWord_1779609).sum := by decide
  have hdescent : baseEnd_1779609 < baseStart_1779609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779644 : List Nat := [2, 2, 2, 5, 1, 1, 3, 2, 1, 1, 3]
def baseStart_1779644 : Nat := 118140960795 + 1779644 * 2 ^ 59
def prefixEnd_1779644 : Nat := 4983230072969 + 3 ^ 40 * 1779644 * 2
def baseEnd_1779644 : Nat := 913812765890140368365573

theorem tailTrace_1779644 : CollatzResearch.WordTrace tailWord_1779644 prefixEnd_1779644 913812765890140368365573 := by
  unfold tailWord_1779644
  simp only [CollatzResearch.WordTrace]
  refine ⟨32454474582330600921244993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43272632776440801228326657 32454474582330600921244993)
  ·
    refine ⟨24340855936747950690933745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32454474582330600921244993 24340855936747950690933745)
    ·
      refine ⟨18255641952560963018200309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24340855936747950690933745 18255641952560963018200309)
      ·
        refine ⟨1711466433052590282956279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18255641952560963018200309 1711466433052590282956279)
        ·
          refine ⟨2567199649578885424434419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1711466433052590282956279 2567199649578885424434419)
          ·
            refine ⟨3850799474368328136651629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2567199649578885424434419 3850799474368328136651629)
            ·
              refine ⟨1444049802888123051244361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3850799474368328136651629 1444049802888123051244361)
              ·
                refine ⟨1083037352166092288433271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1444049802888123051244361 1083037352166092288433271)
                ·
                  refine ⟨1624556028249138432649907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1083037352166092288433271 1624556028249138432649907)
                  ·
                    refine ⟨2436834042373707648974861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1624556028249138432649907 2436834042373707648974861)
                    ·
                      refine ⟨913812765890140368365573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2436834042373707648974861 913812765890140368365573)
                      ·
                        rfl

theorem cell23_1779644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_1779644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1779644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1779644 prefixEnd_1779644 := by exact prefixLift 1779644
  have htrace : WordTrace (prefixWord ++ tailWord_1779644) baseStart_1779644 baseEnd_1779644 := by
    simpa [prefixWord, tailWord_1779644, baseEnd_1779644] using wordTrace_append hprefix tailTrace_1779644
  have hstable : (prefixWord ++ tailWord_1779644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779644).length < 2 ^ (prefixWord ++ tailWord_1779644).sum := by decide
  have hdescent : baseEnd_1779644 < baseStart_1779644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779660 : List Nat := [2, 2, 1, 4, 1, 4, 2, 1, 2, 4]
def baseStart_1779660 : Nat := 118140960795 + 1779660 * 2 ^ 59
def prefixEnd_1779660 : Nat := 4983230072969 + 3 ^ 40 * 1779660 * 2
def baseEnd_1779660 : Nat := 304606993860204101921833

theorem tailTrace_1779660 : CollatzResearch.WordTrace tailWord_1779660 prefixEnd_1779660 304606993860204101921833 := by
  unfold tailWord_1779660
  simp only [CollatzResearch.WordTrace]
  refine ⟨32454766366301618287536217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43273021821735491050048289 32454766366301618287536217)
  ·
    refine ⟨24341074774726213715652163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32454766366301618287536217 24341074774726213715652163)
    ·
      refine ⟨36511612162089320573478245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24341074774726213715652163 36511612162089320573478245)
      ·
        refine ⟨6845927280391747607527171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36511612162089320573478245 6845927280391747607527171)
        ·
          refine ⟨10268890920587621411290757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6845927280391747607527171 10268890920587621411290757)
          ·
            refine ⟨1925417047610179014617017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10268890920587621411290757 1925417047610179014617017)
            ·
              refine ⟨1444062785707634260962763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1925417047610179014617017 1444062785707634260962763)
              ·
                refine ⟨2166094178561451391444145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1444062785707634260962763 2166094178561451391444145)
                ·
                  refine ⟨1624570633921088543583109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2166094178561451391444145 1624570633921088543583109)
                  ·
                    refine ⟨304606993860204101921833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1624570633921088543583109 304606993860204101921833)
                    ·
                      rfl

theorem cell23_1779660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 1, 2, 4].length) (baseStart_1779660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1779660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1779660 prefixEnd_1779660 := by exact prefixLift 1779660
  have htrace : WordTrace (prefixWord ++ tailWord_1779660) baseStart_1779660 baseEnd_1779660 := by
    simpa [prefixWord, tailWord_1779660, baseEnd_1779660] using wordTrace_append hprefix tailTrace_1779660
  have hstable : (prefixWord ++ tailWord_1779660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779660).length < 2 ^ (prefixWord ++ tailWord_1779660).sum := by decide
  have hdescent : baseEnd_1779660 < baseStart_1779660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779670 : List Nat := [5, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3]
def baseStart_1779670 : Nat := 118140960795 + 1779670 * 2 ^ 59
def prefixEnd_1779670 : Nat := 4983230072969 + 3 ^ 40 * 1779670 * 2
def baseEnd_1779670 : Nat := 913826116387157266640453

theorem tailTrace_1779670 : CollatzResearch.WordTrace tailWord_1779670 prefixEnd_1779670 913826116387157266640453 := by
  unfold tailWord_1779670
  simp only [CollatzResearch.WordTrace]
  refine ⟨4056868591410438017683529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43273264975044672188624309 4056868591410438017683529)
  ·
    refine ⟨3042651443557828513262647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4056868591410438017683529 3042651443557828513262647)
    ·
      refine ⟨4563977165336742769893971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3042651443557828513262647 4563977165336742769893971)
      ·
        refine ⟨6845965748005114154840957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4563977165336742769893971 6845965748005114154840957)
        ·
          refine ⟨2567237155501917808065359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6845965748005114154840957 2567237155501917808065359)
          ·
            refine ⟨3850855733252876712098039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2567237155501917808065359 3850855733252876712098039)
            ·
              refine ⟨5776283599879315068147059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3850855733252876712098039 5776283599879315068147059)
              ·
                refine ⟨8664425399818972602220589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5776283599879315068147059 8664425399818972602220589)
                ·
                  refine ⟨3249159524932114725832721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8664425399818972602220589 3249159524932114725832721)
                  ·
                    refine ⟨2436869643699086044374541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3249159524932114725832721 2436869643699086044374541)
                    ·
                      refine ⟨913826116387157266640453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2436869643699086044374541 913826116387157266640453)
                      ·
                        rfl

theorem cell23_1779670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_1779670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1779670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1779670 prefixEnd_1779670 := by exact prefixLift 1779670
  have htrace : WordTrace (prefixWord ++ tailWord_1779670) baseStart_1779670 baseEnd_1779670 := by
    simpa [prefixWord, tailWord_1779670, baseEnd_1779670] using wordTrace_append hprefix tailTrace_1779670
  have hstable : (prefixWord ++ tailWord_1779670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779670).length < 2 ^ (prefixWord ++ tailWord_1779670).sum := by decide
  have hdescent : baseEnd_1779670 < baseStart_1779670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779709 : List Nat := [1, 4, 1, 1, 1, 2, 2, 2, 1, 3, 5]
def baseStart_1779709 : Nat := 118140960795 + 1779709 * 2 ^ 59
def prefixEnd_1779709 : Nat := 4983230072969 + 3 ^ 40 * 1779709 * 2
def baseEnd_1779709 : Nat := 913846142132682614052773

theorem tailTrace_1779709 : CollatzResearch.WordTrace tailWord_1779709 prefixEnd_1779709 913846142132682614052773 := by
  unfold tailWord_1779709
  simp only [CollatzResearch.WordTrace]
  refine ⟨64911319909425717943606181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43274213272950478629070787 64911319909425717943606181)
  ·
    refine ⟨12170872483017322114426159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64911319909425717943606181 12170872483017322114426159)
    ·
      refine ⟨18256308724525983171639239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12170872483017322114426159 18256308724525983171639239)
      ·
        refine ⟨27384463086788974757458859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18256308724525983171639239 27384463086788974757458859)
        ·
          refine ⟨41076694630183462136188289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27384463086788974757458859 41076694630183462136188289)
          ·
            refine ⟨30807520972637596602141217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41076694630183462136188289 30807520972637596602141217)
            ·
              refine ⟨23105640729478197451605913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30807520972637596602141217 23105640729478197451605913)
              ·
                refine ⟨17329230547108648088704435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23105640729478197451605913 17329230547108648088704435)
                ·
                  refine ⟨25993845820662972133056653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17329230547108648088704435 25993845820662972133056653)
                  ·
                    refine ⟨9747692182748614549896245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25993845820662972133056653 9747692182748614549896245)
                    ·
                      refine ⟨913846142132682614052773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9747692182748614549896245 913846142132682614052773)
                      ·
                        rfl

theorem cell23_1779709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_1779709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1779709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1779709 prefixEnd_1779709 := by exact prefixLift 1779709
  have htrace : WordTrace (prefixWord ++ tailWord_1779709) baseStart_1779709 baseEnd_1779709 := by
    simpa [prefixWord, tailWord_1779709, baseEnd_1779709] using wordTrace_append hprefix tailTrace_1779709
  have hstable : (prefixWord ++ tailWord_1779709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779709).length < 2 ^ (prefixWord ++ tailWord_1779709).sum := by decide
  have hdescent : baseEnd_1779709 < baseStart_1779709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779710 : List Nat := [4, 2, 2, 2, 1, 1, 1, 2, 3, 3, 2]
def baseStart_1779710 : Nat := 118140960795 + 1779710 * 2 ^ 59
def prefixEnd_1779710 : Nat := 4983230072969 + 3 ^ 40 * 1779710 * 2
def baseEnd_1779710 : Nat := 913846655613337110140269

theorem tailTrace_1779710 : CollatzResearch.WordTrace tailWord_1779710 prefixEnd_1779710 913846655613337110140269 := by
  unfold tailWord_1779710
  simp only [CollatzResearch.WordTrace]
  refine ⟨8113919547802761889299073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43274237588281396742928389 8113919547802761889299073)
  ·
    refine ⟨6085439660852071416974305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8113919547802761889299073 6085439660852071416974305)
    ·
      refine ⟨4564079745639053562730729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6085439660852071416974305 4564079745639053562730729)
      ·
        refine ⟨3423059809229290172048047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4564079745639053562730729 3423059809229290172048047)
        ·
          refine ⟨5134589713843935258072071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3423059809229290172048047 5134589713843935258072071)
          ·
            refine ⟨7701884570765902887108107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5134589713843935258072071 7701884570765902887108107)
            ·
              refine ⟨11552826856148854330662161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7701884570765902887108107 11552826856148854330662161)
              ·
                refine ⟨8664620142111640747996621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11552826856148854330662161 8664620142111640747996621)
                ·
                  refine ⟨3249232553291865280498733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8664620142111640747996621 3249232553291865280498733)
                  ·
                    refine ⟨1218462207484449480187025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3249232553291865280498733 1218462207484449480187025)
                    ·
                      refine ⟨913846655613337110140269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1218462207484449480187025 913846655613337110140269)
                      ·
                        rfl

theorem cell23_1779710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_1779710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1779710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1779710 prefixEnd_1779710 := by exact prefixLift 1779710
  have htrace : WordTrace (prefixWord ++ tailWord_1779710) baseStart_1779710 baseEnd_1779710 := by
    simpa [prefixWord, tailWord_1779710, baseEnd_1779710] using wordTrace_append hprefix tailTrace_1779710
  have hstable : (prefixWord ++ tailWord_1779710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779710).length < 2 ^ (prefixWord ++ tailWord_1779710).sum := by decide
  have hdescent : baseEnd_1779710 < baseStart_1779710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779723 : List Nat := [1, 1, 1, 1, 6, 1, 4, 1, 1, 4, 2]
def baseStart_1779723 : Nat := 118140960795 + 1779723 * 2 ^ 59
def prefixEnd_1779723 : Nat := 4983230072969 + 3 ^ 40 * 1779723 * 2
def baseEnd_1779723 : Nat := 913853330861845559277709

theorem tailTrace_1779723 : CollatzResearch.WordTrace tailWord_1779723 prefixEnd_1779723 913853330861845559277709 := by
  unfold tailWord_1779723
  simp only [CollatzResearch.WordTrace]
  refine ⟨64911830531374998334615823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43274553687583332223077215 64911830531374998334615823)
  ·
    refine ⟨97367745797062497501923735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64911830531374998334615823 97367745797062497501923735)
    ·
      refine ⟨146051618695593746252885603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97367745797062497501923735 146051618695593746252885603)
      ·
        refine ⟨219077428043390619379328405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146051618695593746252885603 219077428043390619379328405)
        ·
          refine ⟨10269254439533935283406019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 219077428043390619379328405 10269254439533935283406019)
          ·
            refine ⟨15403881659300902925109029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10269254439533935283406019 15403881659300902925109029)
            ·
              refine ⟨2888227811118919298457943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15403881659300902925109029 2888227811118919298457943)
              ·
                refine ⟨4332341716678378947686915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2888227811118919298457943 4332341716678378947686915)
                ·
                  refine ⟨6498512575017568421530373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4332341716678378947686915 6498512575017568421530373)
                  ·
                    refine ⟨1218471107815794079036945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6498512575017568421530373 1218471107815794079036945)
                    ·
                      refine ⟨913853330861845559277709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1218471107815794079036945 913853330861845559277709)
                      ·
                        rfl

theorem cell23_1779723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 1, 1, 4, 2].length) (baseStart_1779723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1779723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1779723 prefixEnd_1779723 := by exact prefixLift 1779723
  have htrace : WordTrace (prefixWord ++ tailWord_1779723) baseStart_1779723 baseEnd_1779723 := by
    simpa [prefixWord, tailWord_1779723, baseEnd_1779723] using wordTrace_append hprefix tailTrace_1779723
  have hstable : (prefixWord ++ tailWord_1779723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779723).length < 2 ^ (prefixWord ++ tailWord_1779723).sum := by decide
  have hdescent : baseEnd_1779723 < baseStart_1779723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779726 : List Nat := [4, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3]
def baseStart_1779726 : Nat := 118140960795 + 1779726 * 2 ^ 59
def prefixEnd_1779726 : Nat := 4983230072969 + 3 ^ 40 * 1779726 * 2
def baseEnd_1779726 : Nat := 913854871303809047540195

theorem tailTrace_1779726 : CollatzResearch.WordTrace tailWord_1779726 prefixEnd_1779726 913854871303809047540195 := by
  unfold tailWord_1779726
  simp only [CollatzResearch.WordTrace]
  refine ⟨8113992493795516230871879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43274626633576086564650021 8113992493795516230871879)
  ·
    refine ⟨12170988740693274346307819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8113992493795516230871879 12170988740693274346307819)
    ·
      refine ⟨18256483111039911519461729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12170988740693274346307819 18256483111039911519461729)
      ·
        refine ⟨13692362333279933639596297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18256483111039911519461729 13692362333279933639596297)
        ·
          refine ⟨10269271749959950229697223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13692362333279933639596297 10269271749959950229697223)
          ·
            refine ⟨15403907624939925344545835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10269271749959950229697223 15403907624939925344545835)
            ·
              refine ⟨23105861437409888016818753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15403907624939925344545835 23105861437409888016818753)
              ·
                refine ⟨17329396078057416012614065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23105861437409888016818753 17329396078057416012614065)
                ·
                  refine ⟨12997047058543062009460549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17329396078057416012614065 12997047058543062009460549)
                  ·
                    refine ⟨2436946323476824126773853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12997047058543062009460549 2436946323476824126773853)
                    ·
                      refine ⟨913854871303809047540195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2436946323476824126773853 913854871303809047540195)
                      ·
                        rfl

theorem cell23_1779726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_1779726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1779726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1779726 prefixEnd_1779726 := by exact prefixLift 1779726
  have htrace : WordTrace (prefixWord ++ tailWord_1779726) baseStart_1779726 baseEnd_1779726 := by
    simpa [prefixWord, tailWord_1779726, baseEnd_1779726] using wordTrace_append hprefix tailTrace_1779726
  have hstable : (prefixWord ++ tailWord_1779726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779726).length < 2 ^ (prefixWord ++ tailWord_1779726).sum := by decide
  have hdescent : baseEnd_1779726 < baseStart_1779726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779774 : List Nat := [4, 2, 1, 3, 3, 1, 1, 1, 1, 4, 2]
def baseStart_1779774 : Nat := 118140960795 + 1779774 * 2 ^ 59
def prefixEnd_1779774 : Nat := 4983230072969 + 3 ^ 40 * 1779774 * 2
def baseEnd_1779774 : Nat := 913879518375224859739975

theorem tailTrace_1779774 : CollatzResearch.WordTrace tailWord_1779774 prefixEnd_1779774 913879518375224859739975 := by
  unfold tailWord_1779774
  simp only [CollatzResearch.WordTrace]
  refine ⟨8114211331773779255590297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43275793769460156029814917 8114211331773779255590297)
  ·
    refine ⟨6085658498830334441692723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8114211331773779255590297 6085658498830334441692723)
    ·
      refine ⟨9128487748245501662539085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6085658498830334441692723 9128487748245501662539085)
      ·
        refine ⟨3423182905592063123452157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9128487748245501662539085 3423182905592063123452157)
        ·
          refine ⟨1283693589597023671294559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3423182905592063123452157 1283693589597023671294559)
          ·
            refine ⟨1925540384395535506941839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1283693589597023671294559 1925540384395535506941839)
            ·
              refine ⟨2888310576593303260412759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1925540384395535506941839 2888310576593303260412759)
              ·
                refine ⟨4332465864889954890619139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2888310576593303260412759 4332465864889954890619139)
                ·
                  refine ⟨6498698797334932335928709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4332465864889954890619139 6498698797334932335928709)
                  ·
                    refine ⟨1218506024500299812986633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6498698797334932335928709 1218506024500299812986633)
                    ·
                      refine ⟨913879518375224859739975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1218506024500299812986633 913879518375224859739975)
                      ·
                        rfl

theorem cell23_1779774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_1779774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1779774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1779774 prefixEnd_1779774 := by exact prefixLift 1779774
  have htrace : WordTrace (prefixWord ++ tailWord_1779774) baseStart_1779774 baseEnd_1779774 := by
    simpa [prefixWord, tailWord_1779774, baseEnd_1779774] using wordTrace_append hprefix tailTrace_1779774
  have hstable : (prefixWord ++ tailWord_1779774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779774).length < 2 ^ (prefixWord ++ tailWord_1779774).sum := by decide
  have hdescent : baseEnd_1779774 < baseStart_1779774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779810 : List Nat := [3, 3, 2, 2, 2, 1, 1, 2, 2, 5]
def baseStart_1779810 : Nat := 118140960795 + 1779810 * 2 ^ 59
def prefixEnd_1779810 : Nat := 4983230072969 + 3 ^ 40 * 1779810 * 2
def baseEnd_1779810 : Nat := 304632667892928906296603

theorem tailTrace_1779810 : CollatzResearch.WordTrace tailWord_1779810 prefixEnd_1779810 304632667892928906296603 := by
  unfold tailWord_1779810
  simp only [CollatzResearch.WordTrace]
  refine ⟨16228750920514953048258221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43276669121373208128688589 16228750920514953048258221)
  ·
    refine ⟨6085781595193107393096833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16228750920514953048258221 6085781595193107393096833)
    ·
      refine ⟨4564336196394830544822625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6085781595193107393096833 4564336196394830544822625)
      ·
        refine ⟨3423252147296122908616969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4564336196394830544822625 3423252147296122908616969)
        ·
          refine ⟨2567439110472092181462727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3423252147296122908616969 2567439110472092181462727)
          ·
            refine ⟨3851158665708138272194091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2567439110472092181462727 3851158665708138272194091)
            ·
              refine ⟨5776737998562207408291137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3851158665708138272194091 5776737998562207408291137)
              ·
                refine ⟨4332553498921655556218353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5776737998562207408291137 4332553498921655556218353)
                ·
                  refine ⟨3249415124191241667163765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4332553498921655556218353 3249415124191241667163765)
                  ·
                    refine ⟨304632667892928906296603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3249415124191241667163765 304632667892928906296603)
                    ·
                      rfl

theorem cell23_1779810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_1779810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1779810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1779810 prefixEnd_1779810 := by exact prefixLift 1779810
  have htrace : WordTrace (prefixWord ++ tailWord_1779810) baseStart_1779810 baseEnd_1779810 := by
    simpa [prefixWord, tailWord_1779810, baseEnd_1779810] using wordTrace_append hprefix tailTrace_1779810
  have hstable : (prefixWord ++ tailWord_1779810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779810).length < 2 ^ (prefixWord ++ tailWord_1779810).sum := by decide
  have hdescent : baseEnd_1779810 < baseStart_1779810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779813 : List Nat := [1, 3, 1, 3, 2, 3, 1, 2, 2, 1, 4]
def baseStart_1779813 : Nat := 118140960795 + 1779813 * 2 ^ 59
def prefixEnd_1779813 : Nat := 4983230072969 + 3 ^ 40 * 1779813 * 2
def baseEnd_1779813 : Nat := 913899544120750207152295

theorem tailTrace_1779813 : CollatzResearch.WordTrace tailWord_1779813 prefixEnd_1779813 913899544120750207152295 := by
  unfold tailWord_1779813
  simp only [CollatzResearch.WordTrace]
  refine ⟨64915113101048943705392093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43276742067365962470261395 64915113101048943705392093)
  ·
    refine ⟨24343167412893353889522035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64915113101048943705392093 24343167412893353889522035)
    ·
      refine ⟨36514751119340030834283053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24343167412893353889522035 36514751119340030834283053)
      ·
        refine ⟨13693031669752511562856145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36514751119340030834283053 13693031669752511562856145)
        ·
          refine ⟨10269773752314383672142109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13693031669752511562856145 10269773752314383672142109)
          ·
            refine ⟨3851165157117893877053291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10269773752314383672142109 3851165157117893877053291)
            ·
              refine ⟨5776747735676840815579937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3851165157117893877053291 5776747735676840815579937)
              ·
                refine ⟨4332560801757630611684953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5776747735676840815579937 4332560801757630611684953)
                ·
                  refine ⟨3249420601318222958763715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4332560801757630611684953 3249420601318222958763715)
                  ·
                    refine ⟨4874130901977334438145573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3249420601318222958763715 4874130901977334438145573)
                    ·
                      refine ⟨913899544120750207152295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4874130901977334438145573 913899544120750207152295)
                      ·
                        rfl

theorem cell23_1779813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_1779813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1779813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1779813 prefixEnd_1779813 := by exact prefixLift 1779813
  have htrace : WordTrace (prefixWord ++ tailWord_1779813) baseStart_1779813 baseEnd_1779813 := by
    simpa [prefixWord, tailWord_1779813, baseEnd_1779813] using wordTrace_append hprefix tailTrace_1779813
  have hstable : (prefixWord ++ tailWord_1779813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779813).length < 2 ^ (prefixWord ++ tailWord_1779813).sum := by decide
  have hdescent : baseEnd_1779813 < baseStart_1779813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779823 : List Nat := [1, 1, 2, 1, 3, 4, 3, 1, 3, 4]
def baseStart_1779823 : Nat := 118140960795 + 1779823 * 2 ^ 59
def prefixEnd_1779823 : Nat := 4983230072969 + 3 ^ 40 * 1779823 * 2
def baseEnd_1779823 : Nat := 304634892975765056009083

theorem tailTrace_1779823 : CollatzResearch.WordTrace tailWord_1779823 prefixEnd_1779823 304634892975765056009083 := by
  unfold tailWord_1779823
  simp only [CollatzResearch.WordTrace]
  refine ⟨64915477831012715413256123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43276985220675143608837415 64915477831012715413256123)
  ·
    refine ⟨97373216746519073119884185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64915477831012715413256123 97373216746519073119884185)
    ·
      refine ⟨73029912559889304839913139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97373216746519073119884185 73029912559889304839913139)
      ·
        refine ⟨109544868839833957259869709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73029912559889304839913139 109544868839833957259869709)
        ·
          refine ⟨41079325814937733972451141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109544868839833957259869709 41079325814937733972451141)
          ·
            refine ⟨7702373590300825119834589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41079325814937733972451141 7702373590300825119834589)
            ·
              refine ⟨2888390096362809419937971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7702373590300825119834589 2888390096362809419937971)
              ·
                refine ⟨4332585144544214129906957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2888390096362809419937971 4332585144544214129906957)
                ·
                  refine ⟨1624719429204080298715109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4332585144544214129906957 1624719429204080298715109)
                  ·
                    refine ⟨304634892975765056009083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1624719429204080298715109 304634892975765056009083)
                    ·
                      rfl

theorem cell23_1779823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 1, 3, 4].length) (baseStart_1779823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1779823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1779823 prefixEnd_1779823 := by exact prefixLift 1779823
  have htrace : WordTrace (prefixWord ++ tailWord_1779823) baseStart_1779823 baseEnd_1779823 := by
    simpa [prefixWord, tailWord_1779823, baseEnd_1779823] using wordTrace_append hprefix tailTrace_1779823
  have hstable : (prefixWord ++ tailWord_1779823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779823).length < 2 ^ (prefixWord ++ tailWord_1779823).sum := by decide
  have hdescent : baseEnd_1779823 < baseStart_1779823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779850 : List Nat := [3, 1, 2, 3, 1, 3, 2, 1, 2, 2, 3]
def baseStart_1779850 : Nat := 118140960795 + 1779850 * 2 ^ 59
def prefixEnd_1779850 : Nat := 4983230072969 + 3 ^ 40 * 1779850 * 2
def baseEnd_1779850 : Nat := 913918542904966562389625

theorem tailTrace_1779850 : CollatzResearch.WordTrace tailWord_1779850 prefixEnd_1779850 913918542904966562389625 := by
  unfold tailWord_1779850
  simp only [CollatzResearch.WordTrace]
  refine ⟨16229115650478724756122251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43277641734609932682992669 16229115650478724756122251)
  ·
    refine ⟨24343673475718087134183377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16229115650478724756122251 24343673475718087134183377)
    ·
      refine ⟨18257755106788565350637533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24343673475718087134183377 18257755106788565350637533)
      ·
        refine ⟨6846658165045712006489075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18257755106788565350637533 6846658165045712006489075)
        ·
          refine ⟨10269987247568568009733613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6846658165045712006489075 10269987247568568009733613)
          ·
            refine ⟨3851245217838213003650105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10269987247568568009733613 3851245217838213003650105)
            ·
              refine ⟨2888433913378659752737579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3851245217838213003650105 2888433913378659752737579)
              ·
                refine ⟨4332650870067989629106369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2888433913378659752737579 4332650870067989629106369)
                ·
                  refine ⟨3249488152550992221829777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4332650870067989629106369 3249488152550992221829777)
                  ·
                    refine ⟨2437116114413244166372333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3249488152550992221829777 2437116114413244166372333)
                    ·
                      refine ⟨913918542904966562389625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2437116114413244166372333 913918542904966562389625)
                      ·
                        rfl

theorem cell23_1779850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_1779850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1779850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1779850 prefixEnd_1779850 := by exact prefixLift 1779850
  have htrace : WordTrace (prefixWord ++ tailWord_1779850) baseStart_1779850 baseEnd_1779850 := by
    simpa [prefixWord, tailWord_1779850, baseEnd_1779850] using wordTrace_append hprefix tailTrace_1779850
  have hstable : (prefixWord ++ tailWord_1779850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779850).length < 2 ^ (prefixWord ++ tailWord_1779850).sum := by decide
  have hdescent : baseEnd_1779850 < baseStart_1779850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779874 : List Nat := [3, 3, 1, 3, 1, 1, 4, 2, 1, 4]
def baseStart_1779874 : Nat := 118140960795 + 1779874 * 2 ^ 59
def prefixEnd_1779874 : Nat := 4983230072969 + 3 ^ 40 * 1779874 * 2
def baseEnd_1779874 : Nat := 304643622146891489496505

theorem tailTrace_1779874 : CollatzResearch.WordTrace tailWord_1779874 prefixEnd_1779874 304643622146891489496505 := by
  unfold tailWord_1779874
  simp only [CollatzResearch.WordTrace]
  refine ⟨16229334488456987780840669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43278225302551967415575117 16229334488456987780840669)
  ·
    refine ⟨6086000433171370417815251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16229334488456987780840669 6086000433171370417815251)
    ·
      refine ⟨9129000649757055626722877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6086000433171370417815251 9129000649757055626722877)
      ·
        refine ⟨3423375243658895860021079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9129000649757055626722877 3423375243658895860021079)
        ·
          refine ⟨5135062865488343790031619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3423375243658895860021079 5135062865488343790031619)
          ·
            refine ⟨7702594298232515685047429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5135062865488343790031619 7702594298232515685047429)
            ·
              refine ⟨1444236430918596690946393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7702594298232515685047429 1444236430918596690946393)
              ·
                refine ⟨1083177323188947518209795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1444236430918596690946393 1083177323188947518209795)
                ·
                  refine ⟨1624765984783421277314693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1083177323188947518209795 1624765984783421277314693)
                  ·
                    refine ⟨304643622146891489496505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1624765984783421277314693 304643622146891489496505)
                    ·
                      rfl

theorem cell23_1779874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 2, 1, 4].length) (baseStart_1779874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1779874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1779874 prefixEnd_1779874 := by exact prefixLift 1779874
  have htrace : WordTrace (prefixWord ++ tailWord_1779874) baseStart_1779874 baseEnd_1779874 := by
    simpa [prefixWord, tailWord_1779874, baseEnd_1779874] using wordTrace_append hprefix tailTrace_1779874
  have hstable : (prefixWord ++ tailWord_1779874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779874).length < 2 ^ (prefixWord ++ tailWord_1779874).sum := by decide
  have hdescent : baseEnd_1779874 < baseStart_1779874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779903 : List Nat := [1, 1, 2, 2, 2, 2, 1, 6, 1, 1, 4]
def baseStart_1779903 : Nat := 118140960795 + 1779903 * 2 ^ 59
def prefixEnd_1779903 : Nat := 4983230072969 + 3 ^ 40 * 1779903 * 2
def baseEnd_1779903 : Nat := 913945757379654855026881

theorem tailTrace_1779903 : CollatzResearch.WordTrace tailWord_1779903 prefixEnd_1779903 913945757379654855026881 := by
  unfold tailWord_1779903
  simp only [CollatzResearch.WordTrace]
  refine ⟨64918395670722889076168363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43278930447148592717445575 64918395670722889076168363)
  ·
    refine ⟨97377593506084333614252545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64918395670722889076168363 97377593506084333614252545)
    ·
      refine ⟨73033195129563250210689409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97377593506084333614252545 73033195129563250210689409)
      ·
        refine ⟨54774896347172437658017057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73033195129563250210689409 54774896347172437658017057)
        ·
          refine ⟨41081172260379328243512793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54774896347172437658017057 41081172260379328243512793)
          ·
            refine ⟨30810879195284496182634595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41081172260379328243512793 30810879195284496182634595)
            ·
              refine ⟨46216318792926744273951893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30810879195284496182634595 46216318792926744273951893)
              ·
                refine ⟨2166389943418441137841495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46216318792926744273951893 2166389943418441137841495)
                ·
                  refine ⟨3249584915127661706762243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2166389943418441137841495 3249584915127661706762243)
                  ·
                    refine ⟨4874377372691492560143365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3249584915127661706762243 4874377372691492560143365)
                    ·
                      refine ⟨913945757379654855026881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4874377372691492560143365 913945757379654855026881)
                      ·
                        rfl

theorem cell23_1779903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 6, 1, 1, 4].length) (baseStart_1779903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1779903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1779903 prefixEnd_1779903 := by exact prefixLift 1779903
  have htrace : WordTrace (prefixWord ++ tailWord_1779903) baseStart_1779903 baseEnd_1779903 := by
    simpa [prefixWord, tailWord_1779903, baseEnd_1779903] using wordTrace_append hprefix tailTrace_1779903
  have hstable : (prefixWord ++ tailWord_1779903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779903).length < 2 ^ (prefixWord ++ tailWord_1779903).sum := by decide
  have hdescent : baseEnd_1779903 < baseStart_1779903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779930 : List Nat := [3, 1, 1, 2, 2, 1, 5, 2, 2, 4]
def baseStart_1779930 : Nat := 118140960795 + 1779930 * 2 ^ 59
def prefixEnd_1779930 : Nat := 4983230072969 + 3 ^ 40 * 1779930 * 2
def baseEnd_1779930 : Nat := 304653207119108749796419

theorem tailTrace_1779930 : CollatzResearch.WordTrace tailWord_1779930 prefixEnd_1779930 304653207119108749796419 := by
  unfold tailWord_1779930
  simp only [CollatzResearch.WordTrace]
  refine ⟨16229845110406268171850311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43279586961083381791600829 16229845110406268171850311)
  ·
    refine ⟨24344767665609402257775467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16229845110406268171850311 24344767665609402257775467)
    ·
      refine ⟨36517151498414103386663201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24344767665609402257775467 36517151498414103386663201)
      ·
        refine ⟨27387863623810577539997401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36517151498414103386663201 27387863623810577539997401)
        ·
          refine ⟨20540897717857933154998051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27387863623810577539997401 20540897717857933154998051)
          ·
            refine ⟨30811346576786899732497077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20540897717857933154998051 30811346576786899732497077)
            ·
              refine ⟨2888563741573771849921601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30811346576786899732497077 2888563741573771849921601)
              ·
                refine ⟨2166422806180328887441201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2888563741573771849921601 2166422806180328887441201)
                ·
                  refine ⟨1624817104635246665580901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2166422806180328887441201 1624817104635246665580901)
                  ·
                    refine ⟨304653207119108749796419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1624817104635246665580901 304653207119108749796419)
                    ·
                      rfl

theorem cell23_1779930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 2, 2, 4].length) (baseStart_1779930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1779930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1779930 prefixEnd_1779930 := by exact prefixLift 1779930
  have htrace : WordTrace (prefixWord ++ tailWord_1779930) baseStart_1779930 baseEnd_1779930 := by
    simpa [prefixWord, tailWord_1779930, baseEnd_1779930] using wordTrace_append hprefix tailTrace_1779930
  have hstable : (prefixWord ++ tailWord_1779930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779930).length < 2 ^ (prefixWord ++ tailWord_1779930).sum := by decide
  have hdescent : baseEnd_1779930 < baseStart_1779930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779937 : List Nat := [1, 2, 3, 1, 3, 1, 4, 1, 3, 2, 2]
def baseStart_1779937 : Nat := 118140960795 + 1779937 * 2 ^ 59
def prefixEnd_1779937 : Nat := 4983230072969 + 3 ^ 40 * 1779937 * 2
def baseEnd_1779937 : Nat := 913963215721907722001725

theorem tailTrace_1779937 : CollatzResearch.WordTrace tailWord_1779937 prefixEnd_1779937 913963215721907722001725 := by
  unfold tailWord_1779937
  simp only [CollatzResearch.WordTrace]
  refine ⟨64919635752599712882906065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43279757168399808588604043 64919635752599712882906065)
  ·
    refine ⟨48689726814449784662179549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64919635752599712882906065 48689726814449784662179549)
    ·
      refine ⟨18258647555418669248317331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48689726814449784662179549 18258647555418669248317331)
      ·
        refine ⟨27387971333128003872475997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18258647555418669248317331 27387971333128003872475997)
        ·
          refine ⟨10270489249923001452178499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27387971333128003872475997 10270489249923001452178499)
          ·
            refine ⟨15405733874884502178267749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10270489249923001452178499 15405733874884502178267749)
            ·
              refine ⟨2888575101540844158425203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15405733874884502178267749 2888575101540844158425203)
              ·
                refine ⟨4332862652311266237637805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2888575101540844158425203 4332862652311266237637805)
                ·
                  refine ⟨1624823494616724839114177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4332862652311266237637805 1624823494616724839114177)
                  ·
                    refine ⟨1218617620962543629335633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1624823494616724839114177 1218617620962543629335633)
                    ·
                      refine ⟨913963215721907722001725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1218617620962543629335633 913963215721907722001725)
                      ·
                        rfl

theorem cell23_1779937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 1, 3, 2, 2].length) (baseStart_1779937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1779937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1779937 prefixEnd_1779937 := by exact prefixLift 1779937
  have htrace : WordTrace (prefixWord ++ tailWord_1779937) baseStart_1779937 baseEnd_1779937 := by
    simpa [prefixWord, tailWord_1779937, baseEnd_1779937] using wordTrace_append hprefix tailTrace_1779937
  have hstable : (prefixWord ++ tailWord_1779937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779937).length < 2 ^ (prefixWord ++ tailWord_1779937).sum := by decide
  have hdescent : baseEnd_1779937 < baseStart_1779937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1779963 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 4, 7, 2]
def baseStart_1779963 : Nat := 118140960795 + 1779963 * 2 ^ 59
def prefixEnd_1779963 : Nat := 4983230072969 + 3 ^ 40 * 1779963 * 2
def baseEnd_1779963 : Nat := 913976566218924620276605

theorem tailTrace_1779963 : CollatzResearch.WordTrace tailWord_1779963 prefixEnd_1779963 913976566218924620276605 := by
  unfold tailWord_1779963
  simp only [CollatzResearch.WordTrace]
  refine ⟨64920584050505519323352543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43280389367003679548901695 64920584050505519323352543)
  ·
    refine ⟨97380876075758278985028815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64920584050505519323352543 97380876075758278985028815)
    ·
      refine ⟨146071314113637418477543223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97380876075758278985028815 146071314113637418477543223)
      ·
        refine ⟨219106971170456127716314835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146071314113637418477543223 219106971170456127716314835)
        ·
          refine ⟨328660456755684191574472253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219106971170456127716314835 328660456755684191574472253)
          ·
            refine ⟨123247671283381571840427095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 328660456755684191574472253 123247671283381571840427095)
            ·
              refine ⟨184871506925072357760640643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123247671283381571840427095 184871506925072357760640643)
              ·
                refine ⟨277307260387608536640960965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184871506925072357760640643 277307260387608536640960965)
                ·
                  refine ⟨51995111322676600620180181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 277307260387608536640960965 51995111322676600620180181)
                  ·
                    refine ⟨1218635421625232827035473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51995111322676600620180181 1218635421625232827035473)
                    ·
                      refine ⟨913976566218924620276605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1218635421625232827035473 913976566218924620276605)
                      ·
                        rfl

theorem cell23_1779963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 7, 2].length) (baseStart_1779963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1779963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1779963 prefixEnd_1779963 := by exact prefixLift 1779963
  have htrace : WordTrace (prefixWord ++ tailWord_1779963) baseStart_1779963 baseEnd_1779963 := by
    simpa [prefixWord, tailWord_1779963, baseEnd_1779963] using wordTrace_append hprefix tailTrace_1779963
  have hstable : (prefixWord ++ tailWord_1779963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1779963).length < 2 ^ (prefixWord ++ tailWord_1779963).sum := by decide
  have hdescent : baseEnd_1779963 < baseStart_1779963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1779963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780004 : List Nat := [2, 3, 1, 3, 1, 2, 4, 1, 2, 1, 3]
def baseStart_1780004 : Nat := 118140960795 + 1780004 * 2 ^ 59
def prefixEnd_1780004 : Nat := 4983230072969 + 3 ^ 40 * 1780004 * 2
def baseEnd_1780004 : Nat := 913997618925758959863917

theorem tailTrace_1780004 : CollatzResearch.WordTrace tailWord_1780004 prefixEnd_1780004 913997618925758959863917 := by
  unfold tailWord_1780004
  simp only [CollatzResearch.WordTrace]
  refine ⟨32461039721678491662797533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43281386295571322217063377 32461039721678491662797533)
  ·
    refine ⟨12172889895629434373549075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32461039721678491662797533 12172889895629434373549075)
    ·
      refine ⟨18259334843444151560323613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12172889895629434373549075 18259334843444151560323613)
      ·
        refine ⟨6847250566291556835121355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18259334843444151560323613 6847250566291556835121355)
        ·
          refine ⟨10270875849437335252682033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6847250566291556835121355 10270875849437335252682033)
          ·
            refine ⟨7703156887078001439511525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10270875849437335252682033 7703156887078001439511525)
            ·
              refine ⟨1444341916327125269908411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7703156887078001439511525 1444341916327125269908411)
              ·
                refine ⟨2166512874490687904862617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1444341916327125269908411 2166512874490687904862617)
                ·
                  refine ⟨1624884655868015928646963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2166512874490687904862617 1624884655868015928646963)
                  ·
                    refine ⟨2437326983802023892970445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1624884655868015928646963 2437326983802023892970445)
                    ·
                      refine ⟨913997618925758959863917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2437326983802023892970445 913997618925758959863917)
                      ·
                        rfl

theorem cell23_1780004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_1780004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1780004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1780004 prefixEnd_1780004 := by exact prefixLift 1780004
  have htrace : WordTrace (prefixWord ++ tailWord_1780004) baseStart_1780004 baseEnd_1780004 := by
    simpa [prefixWord, tailWord_1780004, baseEnd_1780004] using wordTrace_append hprefix tailTrace_1780004
  have hstable : (prefixWord ++ tailWord_1780004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780004).length < 2 ^ (prefixWord ++ tailWord_1780004).sum := by decide
  have hdescent : baseEnd_1780004 < baseStart_1780004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780030 : List Nat := [4, 2, 1, 2, 1, 2, 2, 1, 2, 1, 5]
def baseStart_1780030 : Nat := 118140960795 + 1780030 * 2 ^ 59
def prefixEnd_1780030 : Nat := 4983230072969 + 3 ^ 40 * 1780030 * 2
def baseEnd_1780030 : Nat := 914010969422775858138797

theorem tailTrace_1780030 : CollatzResearch.WordTrace tailWord_1780030 prefixEnd_1780030 914010969422775858138797 := by
  unfold tailWord_1780030
  simp only [CollatzResearch.WordTrace]
  refine ⟨8115378467657848720755193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43282018494175193177361029 8115378467657848720755193)
  ·
    refine ⟨6086533850743386540566395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8115378467657848720755193 6086533850743386540566395)
    ·
      refine ⟨9129800776115079810849593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6086533850743386540566395 9129800776115079810849593)
      ·
        refine ⟨6847350582086309858137195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9129800776115079810849593 6847350582086309858137195)
        ·
          refine ⟨10271025873129464787205793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6847350582086309858137195 10271025873129464787205793)
          ·
            refine ⟨7703269404847098590404345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10271025873129464787205793 7703269404847098590404345)
            ·
              refine ⟨5777452053635323942803259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7703269404847098590404345 5777452053635323942803259)
              ·
                refine ⟨8666178080452985914204889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5777452053635323942803259 8666178080452985914204889)
                ·
                  refine ⟨6499633560339739435653667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8666178080452985914204889 6499633560339739435653667)
                  ·
                    refine ⟨9749450340509609153480501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6499633560339739435653667 9749450340509609153480501)
                    ·
                      refine ⟨914010969422775858138797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9749450340509609153480501 914010969422775858138797)
                      ·
                        rfl

theorem cell23_1780030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_1780030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1780030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1780030 prefixEnd_1780030 := by exact prefixLift 1780030
  have htrace : WordTrace (prefixWord ++ tailWord_1780030) baseStart_1780030 baseEnd_1780030 := by
    simpa [prefixWord, tailWord_1780030, baseEnd_1780030] using wordTrace_append hprefix tailTrace_1780030
  have hstable : (prefixWord ++ tailWord_1780030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780030).length < 2 ^ (prefixWord ++ tailWord_1780030).sum := by decide
  have hdescent : baseEnd_1780030 < baseStart_1780030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780044 : List Nat := [2, 2, 1, 3, 2, 1, 4, 2, 2, 2, 2]
def baseStart_1780044 : Nat := 118140960795 + 1780044 * 2 ^ 59
def prefixEnd_1780044 : Nat := 4983230072969 + 3 ^ 40 * 1780044 * 2
def baseEnd_1780044 : Nat := 914018158151938803363733

theorem tailTrace_1780044 : CollatzResearch.WordTrace tailWord_1780044 prefixEnd_1780044 914018158151938803363733 := by
  unfold tailWord_1780044
  simp only [CollatzResearch.WordTrace]
  refine ⟨32461769181606035078525593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43282358908808046771367457 32461769181606035078525593)
  ·
    refine ⟨24346326886204526308894195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32461769181606035078525593 24346326886204526308894195)
    ·
      refine ⟨36519490329306789463341293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24346326886204526308894195 36519490329306789463341293)
      ·
        refine ⟨13694808873490046048752985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36519490329306789463341293 13694808873490046048752985)
        ·
          refine ⟨10271106655117534536564739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13694808873490046048752985 10271106655117534536564739)
          ·
            refine ⟨15406659982676301804847109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10271106655117534536564739 15406659982676301804847109)
            ·
              refine ⟨2888748746751806588408833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15406659982676301804847109 2888748746751806588408833)
              ·
                refine ⟨2166561560063854941306625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2888748746751806588408833 2166561560063854941306625)
                ·
                  refine ⟨1624921170047891205979969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2166561560063854941306625 1624921170047891205979969)
                  ·
                    refine ⟨1218690877535918404484977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1624921170047891205979969 1218690877535918404484977)
                    ·
                      refine ⟨914018158151938803363733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1218690877535918404484977 914018158151938803363733)
                      ·
                        rfl

theorem cell23_1780044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 2, 2, 2, 2].length) (baseStart_1780044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1780044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1780044 prefixEnd_1780044 := by exact prefixLift 1780044
  have htrace : WordTrace (prefixWord ++ tailWord_1780044) baseStart_1780044 baseEnd_1780044 := by
    simpa [prefixWord, tailWord_1780044, baseEnd_1780044] using wordTrace_append hprefix tailTrace_1780044
  have hstable : (prefixWord ++ tailWord_1780044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780044).length < 2 ^ (prefixWord ++ tailWord_1780044).sum := by decide
  have hdescent : baseEnd_1780044 < baseStart_1780044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780063 : List Nat := [1, 1, 2, 3, 1, 2, 2, 2, 4, 5]
def baseStart_1780063 : Nat := 118140960795 + 1780063 * 2 ^ 59
def prefixEnd_1780063 : Nat := 4983230072969 + 3 ^ 40 * 1780063 * 2
def baseEnd_1780063 : Nat := 304675971428124743008715

theorem tailTrace_1780063 : CollatzResearch.WordTrace tailWord_1780063 prefixEnd_1780063 304675971428124743008715 := by
  unfold tailWord_1780063
  simp only [CollatzResearch.WordTrace]
  refine ⟨64924231350143236401992843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43282820900095490934661895 64924231350143236401992843)
  ·
    refine ⟨97386347025214854602989265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64924231350143236401992843 97386347025214854602989265)
    ·
      refine ⟨73039760268911140952241949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97386347025214854602989265 73039760268911140952241949)
      ·
        refine ⟨27389910100841677857090731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73039760268911140952241949 27389910100841677857090731)
        ·
          refine ⟨41084865151262516785636097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27389910100841677857090731 41084865151262516785636097)
          ·
            refine ⟨30813648863446887589227073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41084865151262516785636097 30813648863446887589227073)
            ·
              refine ⟨23110236647585165691920305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30813648863446887589227073 23110236647585165691920305)
              ·
                refine ⟨17332677485688874268940229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23110236647585165691920305 17332677485688874268940229)
                ·
                  refine ⟨3249877028566663925426293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17332677485688874268940229 3249877028566663925426293)
                  ·
                    refine ⟨304675971428124743008715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3249877028566663925426293 304675971428124743008715)
                    ·
                      rfl

theorem cell23_1780063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 4, 5].length) (baseStart_1780063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1780063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1780063 prefixEnd_1780063 := by exact prefixLift 1780063
  have htrace : WordTrace (prefixWord ++ tailWord_1780063) baseStart_1780063 baseEnd_1780063 := by
    simpa [prefixWord, tailWord_1780063, baseEnd_1780063] using wordTrace_append hprefix tailTrace_1780063
  have hstable : (prefixWord ++ tailWord_1780063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780063).length < 2 ^ (prefixWord ++ tailWord_1780063).sum := by decide
  have hdescent : baseEnd_1780063 < baseStart_1780063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780080 : List Nat := [2, 1, 1, 1, 4, 3, 3, 1, 2, 5]
def baseStart_1780080 : Nat := 118140960795 + 1780080 * 2 ^ 59
def prefixEnd_1780080 : Nat := 4983230072969 + 3 ^ 40 * 1780080 * 2
def baseEnd_1780080 : Nat := 304678881151833554171189

theorem tailTrace_1780080 : CollatzResearch.WordTrace tailWord_1780080 prefixEnd_1780080 304678881151833554171189 := by
  unfold tailWord_1780080
  simp only [CollatzResearch.WordTrace]
  refine ⟨32462425695540824152680847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43283234260721098870241129 32462425695540824152680847)
  ·
    refine ⟨48693638543311236229021271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32462425695540824152680847 48693638543311236229021271)
    ·
      refine ⟨73040457814966854343531907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48693638543311236229021271 73040457814966854343531907)
      ·
        refine ⟨109560686722450281515297861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73040457814966854343531907 109560686722450281515297861)
        ·
          refine ⟨20542628760459427784118349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109560686722450281515297861 20542628760459427784118349)
          ·
            refine ⟨7703485785172285419044381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20542628760459427784118349 7703485785172285419044381)
            ·
              refine ⟨2888807169439607032141643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7703485785172285419044381 2888807169439607032141643)
              ·
                refine ⟨4333210754159410548212465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2888807169439607032141643 4333210754159410548212465)
                ·
                  refine ⟨3249908065619557911159349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4333210754159410548212465 3249908065619557911159349)
                  ·
                    refine ⟨304678881151833554171189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3249908065619557911159349 304678881151833554171189)
                    ·
                      rfl

theorem cell23_1780080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 1, 2, 5].length) (baseStart_1780080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1780080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1780080 prefixEnd_1780080 := by exact prefixLift 1780080
  have htrace : WordTrace (prefixWord ++ tailWord_1780080) baseStart_1780080 baseEnd_1780080 := by
    simpa [prefixWord, tailWord_1780080, baseEnd_1780080] using wordTrace_append hprefix tailTrace_1780080
  have hstable : (prefixWord ++ tailWord_1780080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780080).length < 2 ^ (prefixWord ++ tailWord_1780080).sum := by decide
  have hdescent : baseEnd_1780080 < baseStart_1780080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780083 : List Nat := [1, 1, 1, 2, 2, 1, 2, 5, 1, 3, 4]
def baseStart_1780083 : Nat := 118140960795 + 1780083 * 2 ^ 59
def prefixEnd_1780083 : Nat := 4983230072969 + 3 ^ 40 * 1780083 * 2
def baseEnd_1780083 : Nat := 914038183897464150776053

theorem tailTrace_1780083 : CollatzResearch.WordTrace tailWord_1780083 prefixEnd_1780083 914038183897464150776053 := by
  unfold tailWord_1780083
  simp only [CollatzResearch.WordTrace]
  refine ⟨64924960810070779817720903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43283307206713853211813935 64924960810070779817720903)
  ·
    refine ⟨97387441215106169726581355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64924960810070779817720903 97387441215106169726581355)
    ·
      refine ⟨146081161822659254589872033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97387441215106169726581355 146081161822659254589872033)
      ·
        refine ⟨109560871366994440942404025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146081161822659254589872033 109560871366994440942404025)
        ·
          refine ⟨82170653525245830706803019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109560871366994440942404025 82170653525245830706803019)
          ·
            refine ⟨123255980287868746060204529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82170653525245830706803019 123255980287868746060204529)
            ·
              refine ⟨92441985215901559545153397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123255980287868746060204529 92441985215901559545153397)
              ·
                refine ⟨8666436113990771207358131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92441985215901559545153397 8666436113990771207358131)
                ·
                  refine ⟨12999654170986156811037197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8666436113990771207358131 12999654170986156811037197)
                  ·
                    refine ⟨4874870314119808804138949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12999654170986156811037197 4874870314119808804138949)
                    ·
                      refine ⟨914038183897464150776053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4874870314119808804138949 914038183897464150776053)
                      ·
                        rfl

theorem cell23_1780083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 3, 4].length) (baseStart_1780083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1780083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1780083 prefixEnd_1780083 := by exact prefixLift 1780083
  have htrace : WordTrace (prefixWord ++ tailWord_1780083) baseStart_1780083 baseEnd_1780083 := by
    simpa [prefixWord, tailWord_1780083, baseEnd_1780083] using wordTrace_append hprefix tailTrace_1780083
  have hstable : (prefixWord ++ tailWord_1780083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780083).length < 2 ^ (prefixWord ++ tailWord_1780083).sum := by decide
  have hdescent : baseEnd_1780083 < baseStart_1780083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780100 : List Nat := [2, 3, 2, 1, 1, 2, 2, 1, 4, 1, 4]
def baseStart_1780100 : Nat := 118140960795 + 1780100 * 2 ^ 59
def prefixEnd_1780100 : Nat := 4983230072969 + 3 ^ 40 * 1780100 * 2
def baseEnd_1780100 : Nat := 914046913068590584263475

theorem tailTrace_1780100 : CollatzResearch.WordTrace tailWord_1780100 prefixEnd_1780100 914046913068590584263475 := by
  unfold tailWord_1780100
  simp only [CollatzResearch.WordTrace]
  refine ⟨32462790425504595860544877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43283720567339461147393169 32462790425504595860544877)
  ·
    refine ⟨12173546409564223447704329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32462790425504595860544877 12173546409564223447704329)
    ·
      refine ⟨9130159807173167585778247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12173546409564223447704329 9130159807173167585778247)
      ·
        refine ⟨13695239710759751378667371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9130159807173167585778247 13695239710759751378667371)
        ·
          refine ⟨20542859566139627068001057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13695239710759751378667371 20542859566139627068001057)
          ·
            refine ⟨15407144674604720301000793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20542859566139627068001057 15407144674604720301000793)
            ·
              refine ⟨11555358505953540225750595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15407144674604720301000793 11555358505953540225750595)
              ·
                refine ⟨17333037758930310338625893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11555358505953540225750595 17333037758930310338625893)
                ·
                  refine ⟨3249944579799433188492355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17333037758930310338625893 3249944579799433188492355)
                  ·
                    refine ⟨4874916869699149782738533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3249944579799433188492355 4874916869699149782738533)
                    ·
                      refine ⟨914046913068590584263475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4874916869699149782738533 914046913068590584263475)
                      ·
                        rfl

theorem cell23_1780100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_1780100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1780100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1780100 prefixEnd_1780100 := by exact prefixLift 1780100
  have htrace : WordTrace (prefixWord ++ tailWord_1780100) baseStart_1780100 baseEnd_1780100 := by
    simpa [prefixWord, tailWord_1780100, baseEnd_1780100] using wordTrace_append hprefix tailTrace_1780100
  have hstable : (prefixWord ++ tailWord_1780100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780100).length < 2 ^ (prefixWord ++ tailWord_1780100).sum := by decide
  have hdescent : baseEnd_1780100 < baseStart_1780100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780113 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 4]
def baseStart_1780113 : Nat := 118140960795 + 1780113 * 2 ^ 59
def prefixEnd_1780113 : Nat := 4983230072969 + 3 ^ 40 * 1780113 * 2
def baseEnd_1780113 : Nat := 914053588317099033400915

theorem tailTrace_1780113 : CollatzResearch.WordTrace tailWord_1780113 prefixEnd_1780113 914053588317099033400915 := by
  unfold tailWord_1780113
  simp only [CollatzResearch.WordTrace]
  refine ⟨64926054999962094941312993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43284036666641396627541995 64926054999962094941312993)
  ·
    refine ⟨48694541249971571205984745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64926054999962094941312993 48694541249971571205984745)
    ·
      refine ⟨36520905937478678404488559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48694541249971571205984745 36520905937478678404488559)
      ·
        refine ⟨54781358906218017606732839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36520905937478678404488559 54781358906218017606732839)
        ·
          refine ⟨82172038359327026410099259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54781358906218017606732839 82172038359327026410099259)
          ·
            refine ⟨123258057538990539615148889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82172038359327026410099259 123258057538990539615148889)
            ·
              refine ⟨92443543154242904711361667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123258057538990539615148889 92443543154242904711361667)
              ·
                refine ⟨138665314731364357067042501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92443543154242904711361667 138665314731364357067042501)
                ·
                  refine ⟨25999746512130816950070469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138665314731364357067042501 25999746512130816950070469)
                  ·
                    refine ⟨4874952471024528178138213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25999746512130816950070469 4874952471024528178138213)
                    ·
                      refine ⟨914053588317099033400915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4874952471024528178138213 914053588317099033400915)
                      ·
                        rfl

theorem cell23_1780113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 4].length) (baseStart_1780113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1780113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1780113 prefixEnd_1780113 := by exact prefixLift 1780113
  have htrace : WordTrace (prefixWord ++ tailWord_1780113) baseStart_1780113 baseEnd_1780113 := by
    simpa [prefixWord, tailWord_1780113, baseEnd_1780113] using wordTrace_append hprefix tailTrace_1780113
  have hstable : (prefixWord ++ tailWord_1780113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780113).length < 2 ^ (prefixWord ++ tailWord_1780113).sum := by decide
  have hdescent : baseEnd_1780113 < baseStart_1780113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780130 : List Nat := [3, 3, 1, 2, 1, 1, 1, 1, 2, 4, 4]
def baseStart_1780130 : Nat := 118140960795 + 1780130 * 2 ^ 59
def prefixEnd_1780130 : Nat := 4983230072969 + 3 ^ 40 * 1780130 * 2
def baseEnd_1780130 : Nat := 914062317488225466888337

theorem tailTrace_1780130 : CollatzResearch.WordTrace tailWord_1780130 prefixEnd_1780130 914062317488225466888337 := by
  unfold tailWord_1780130
  simp only [CollatzResearch.WordTrace]
  refine ⟨16231668760225126711170461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43284450027267004563121229 16231668760225126711170461)
  ·
    refine ⟨6086875785084422516688923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16231668760225126711170461 6086875785084422516688923)
    ·
      refine ⟨9130313677626633775033385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6086875785084422516688923 9130313677626633775033385)
      ·
        refine ⟨6847735258219975331275039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9130313677626633775033385 6847735258219975331275039)
        ·
          refine ⟨10271602887329962996912559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6847735258219975331275039 10271602887329962996912559)
          ·
            refine ⟨15407404330994944495368839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10271602887329962996912559 15407404330994944495368839)
            ·
              refine ⟨23111106496492416743053259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15407404330994944495368839 23111106496492416743053259)
              ·
                refine ⟨34666659744738625114579889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23111106496492416743053259 34666659744738625114579889)
                ·
                  refine ⟨25999994808553968835934917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34666659744738625114579889 25999994808553968835934917)
                  ·
                    refine ⟨4874999026603869156737797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25999994808553968835934917 4874999026603869156737797)
                    ·
                      refine ⟨914062317488225466888337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4874999026603869156737797 914062317488225466888337)
                      ·
                        rfl

theorem cell23_1780130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_1780130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1780130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1780130 prefixEnd_1780130 := by exact prefixLift 1780130
  have htrace : WordTrace (prefixWord ++ tailWord_1780130) baseStart_1780130 baseEnd_1780130 := by
    simpa [prefixWord, tailWord_1780130, baseEnd_1780130] using wordTrace_append hprefix tailTrace_1780130
  have hstable : (prefixWord ++ tailWord_1780130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780130).length < 2 ^ (prefixWord ++ tailWord_1780130).sum := by decide
  have hdescent : baseEnd_1780130 < baseStart_1780130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780163 : List Nat := [1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 7]
def baseStart_1780163 : Nat := 118140960795 + 1780163 * 2 ^ 59
def prefixEnd_1780163 : Nat := 4983230072969 + 3 ^ 40 * 1780163 * 2
def baseEnd_1780163 : Nat := 914079262349823837775685

theorem tailTrace_1780163 : CollatzResearch.WordTrace tailWord_1780163 prefixEnd_1780163 914079262349823837775685 := by
  unfold tailWord_1780163
  simp only [CollatzResearch.WordTrace]
  refine ⟨64927878649780953480633143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43285252433187302320422095 64927878649780953480633143)
  ·
    refine ⟨97391817974671430220949715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64927878649780953480633143 97391817974671430220949715)
    ·
      refine ⟨146087726962007145331424573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97391817974671430220949715 146087726962007145331424573)
      ·
        refine ⟨54782897610752679499284215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146087726962007145331424573 54782897610752679499284215)
        ·
          refine ⟨82174346416129019248926323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54782897610752679499284215 82174346416129019248926323)
          ·
            refine ⟨123261519624193528873389485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82174346416129019248926323 123261519624193528873389485)
            ·
              refine ⟨46223069859072573327521057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123261519624193528873389485 46223069859072573327521057)
              ·
                refine ⟨34667302394304429995640793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46223069859072573327521057 34667302394304429995640793)
                ·
                  refine ⟨26000476795728322496730595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34667302394304429995640793 26000476795728322496730595)
                  ·
                    refine ⟨39000715193592483745095893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26000476795728322496730595 39000715193592483745095893)
                    ·
                      refine ⟨914079262349823837775685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 39000715193592483745095893 914079262349823837775685)
                      ·
                        rfl

theorem cell23_1780163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 7].length) (baseStart_1780163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1780163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1780163 prefixEnd_1780163 := by exact prefixLift 1780163
  have htrace : WordTrace (prefixWord ++ tailWord_1780163) baseStart_1780163 baseEnd_1780163 := by
    simpa [prefixWord, tailWord_1780163, baseEnd_1780163] using wordTrace_append hprefix tailTrace_1780163
  have hstable : (prefixWord ++ tailWord_1780163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780163).length < 2 ^ (prefixWord ++ tailWord_1780163).sum := by decide
  have hdescent : baseEnd_1780163 < baseStart_1780163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780170 : List Nat := [3, 1, 2, 1, 2, 2, 2, 2, 3, 5]
def baseStart_1780170 : Nat := 118140960795 + 1780170 * 2 ^ 59
def prefixEnd_1780170 : Nat := 4983230072969 + 3 ^ 40 * 1780170 * 2
def baseEnd_1780170 : Nat := 304694285571468436796051

theorem tailTrace_1780170 : CollatzResearch.WordTrace tailWord_1780170 prefixEnd_1780170 304694285571468436796051 := by
  unfold tailWord_1780170
  simp only [CollatzResearch.WordTrace]
  refine ⟨16232033490188898419034491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43285422640503729117425309 16232033490188898419034491)
  ·
    refine ⟨24348050235283347628551737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16232033490188898419034491 24348050235283347628551737)
    ·
      refine ⟨18261037676462510721413803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24348050235283347628551737 18261037676462510721413803)
      ·
        refine ⟨27391556514693766082120705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18261037676462510721413803 27391556514693766082120705)
        ·
          refine ⟨20543667386020324561590529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27391556514693766082120705 20543667386020324561590529)
          ·
            refine ⟨15407750539515243421192897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20543667386020324561590529 15407750539515243421192897)
            ·
              refine ⟨11555812904636432565894673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15407750539515243421192897 11555812904636432565894673)
              ·
                refine ⟨8666859678477324424421005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11555812904636432565894673 8666859678477324424421005)
                ·
                  refine ⟨3250072379428996659157877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8666859678477324424421005 3250072379428996659157877)
                  ·
                    refine ⟨304694285571468436796051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3250072379428996659157877 304694285571468436796051)
                    ·
                      rfl

theorem cell23_1780170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 3, 5].length) (baseStart_1780170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1780170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1780170 prefixEnd_1780170 := by exact prefixLift 1780170
  have htrace : WordTrace (prefixWord ++ tailWord_1780170) baseStart_1780170 baseEnd_1780170 := by
    simpa [prefixWord, tailWord_1780170, baseEnd_1780170] using wordTrace_append hprefix tailTrace_1780170
  have hstable : (prefixWord ++ tailWord_1780170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780170).length < 2 ^ (prefixWord ++ tailWord_1780170).sum := by decide
  have hdescent : baseEnd_1780170 < baseStart_1780170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780200 : List Nat := [2, 1, 4, 1, 1, 3, 1, 1, 3, 6]
def baseStart_1780200 : Nat := 118140960795 + 1780200 * 2 ^ 59
def prefixEnd_1780200 : Nat := 4983230072969 + 3 ^ 40 * 1780200 * 2
def baseEnd_1780200 : Nat := 304699420378013397671005

theorem tailTrace_1780200 : CollatzResearch.WordTrace tailWord_1780200 prefixEnd_1780200 304699420378013397671005 := by
  unfold tailWord_1780200
  simp only [CollatzResearch.WordTrace]
  refine ⟨32464614075323454399865027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43286152100431272533153369 32464614075323454399865027)
  ·
    refine ⟨48696921112985181599797541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32464614075323454399865027 48696921112985181599797541)
    ·
      refine ⟨9130672708684721549962039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48696921112985181599797541 9130672708684721549962039)
      ·
        refine ⟨13696009063027082324943059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9130672708684721549962039 13696009063027082324943059)
        ·
          refine ⟨20544013594540623487414589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13696009063027082324943059 20544013594540623487414589)
          ·
            refine ⟨7704005097952733807780471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20544013594540623487414589 7704005097952733807780471)
            ·
              refine ⟨11556007646929100711670707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7704005097952733807780471 11556007646929100711670707)
              ·
                refine ⟨17334011470393651067506061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11556007646929100711670707 17334011470393651067506061)
                ·
                  refine ⟨6500254301397619150314773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17334011470393651067506061 6500254301397619150314773)
                  ·
                    refine ⟨304699420378013397671005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6500254301397619150314773 304699420378013397671005)
                    ·
                      rfl

theorem cell23_1780200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_1780200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1780200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1780200 prefixEnd_1780200 := by exact prefixLift 1780200
  have htrace : WordTrace (prefixWord ++ tailWord_1780200) baseStart_1780200 baseEnd_1780200 := by
    simpa [prefixWord, tailWord_1780200, baseEnd_1780200] using wordTrace_append hprefix tailTrace_1780200
  have hstable : (prefixWord ++ tailWord_1780200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780200).length < 2 ^ (prefixWord ++ tailWord_1780200).sum := by decide
  have hdescent : baseEnd_1780200 < baseStart_1780200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
