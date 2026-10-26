import V185TrunkScan23Chunk0310

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1840149 : List Nat := [1, 3, 2, 1, 4, 3, 1, 3, 5]
def baseStart_1840149 : Nat := 118140960795 + 1840149 * 2 ^ 59
def prefixEnd_1840149 : Nat := 4983230072969 + 3 ^ 40 * 1840149 * 2
def baseEnd_1840149 : Nat := 104986768098936238030535

theorem tailTrace_1840149 : CollatzResearch.WordTrace tailWord_1840149 prefixEnd_1840149 104986768098936238030535 := by
  unfold tailWord_1840149
  simp only [CollatzResearch.WordTrace]
  refine ⟨67115747810461920273803501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44743831873641280182535667 67115747810461920273803501)
  ·
    refine ⟨25168405428923220102676313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67115747810461920273803501 25168405428923220102676313)
    ·
      refine ⟨18876304071692415077007235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25168405428923220102676313 18876304071692415077007235)
      ·
        refine ⟨28314456107538622615510853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18876304071692415077007235 28314456107538622615510853)
        ·
          refine ⟨5308960520163491740408285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28314456107538622615510853 5308960520163491740408285)
          ·
            refine ⟨1990860195061309402653107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5308960520163491740408285 1990860195061309402653107)
            ·
              refine ⟨2986290292591964103979661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1990860195061309402653107 2986290292591964103979661)
              ·
                refine ⟨1119858859721986538992373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2986290292591964103979661 1119858859721986538992373)
                ·
                  refine ⟨104986768098936238030535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1119858859721986538992373 104986768098936238030535)
                  ·
                    rfl

theorem cell23_1840149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 3, 5].length) (baseStart_1840149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1840149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1840149 prefixEnd_1840149 := by exact prefixLift 1840149
  have htrace : WordTrace (prefixWord ++ tailWord_1840149) baseStart_1840149 baseEnd_1840149 := by
    simpa [prefixWord, tailWord_1840149, baseEnd_1840149] using wordTrace_append hprefix tailTrace_1840149
  have hstable : (prefixWord ++ tailWord_1840149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840149).length < 2 ^ (prefixWord ++ tailWord_1840149).sum := by decide
  have hdescent : baseEnd_1840149 < baseStart_1840149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840162 : List Nat := [3, 3, 1, 1, 1, 4, 1, 2, 2, 5]
def baseStart_1840162 : Nat := 118140960795 + 1840162 * 2 ^ 59
def prefixEnd_1840162 : Nat := 4983230072969 + 3 ^ 40 * 1840162 * 2
def baseEnd_1840162 : Nat := 314962529379644863804085

theorem tailTrace_1840162 : CollatzResearch.WordTrace tailWord_1840162 prefixEnd_1840162 314962529379644863804085 := by
  unfold tailWord_1840162
  simp only [CollatzResearch.WordTrace]
  refine ⟨16779055489853705873506685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44744147972943215662684493 16779055489853705873506685)
  ·
    refine ⟨6292145808695139702565007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16779055489853705873506685 6292145808695139702565007)
    ·
      refine ⟨9438218713042709553847511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6292145808695139702565007 9438218713042709553847511)
      ·
        refine ⟨14157328069564064330771267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9438218713042709553847511 14157328069564064330771267)
        ·
          refine ⟨21235992104346096496156901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14157328069564064330771267 21235992104346096496156901)
          ·
            refine ⟨3981748519564893093029419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21235992104346096496156901 3981748519564893093029419)
            ·
              refine ⟨5972622779347339639544129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3981748519564893093029419 5972622779347339639544129)
              ·
                refine ⟨4479467084510504729658097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5972622779347339639544129 4479467084510504729658097)
                ·
                  refine ⟨3359600313382878547243573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4479467084510504729658097 3359600313382878547243573)
                  ·
                    refine ⟨314962529379644863804085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3359600313382878547243573 314962529379644863804085)
                    ·
                      rfl

theorem cell23_1840162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_1840162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1840162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1840162 prefixEnd_1840162 := by exact prefixLift 1840162
  have htrace : WordTrace (prefixWord ++ tailWord_1840162) baseStart_1840162 baseEnd_1840162 := by
    simpa [prefixWord, tailWord_1840162, baseEnd_1840162] using wordTrace_append hprefix tailTrace_1840162
  have hstable : (prefixWord ++ tailWord_1840162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840162).length < 2 ^ (prefixWord ++ tailWord_1840162).sum := by decide
  have hdescent : baseEnd_1840162 < baseStart_1840162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840202 : List Nat := [3, 1, 2, 1, 1, 2, 3, 3, 2, 2, 3]
def baseStart_1840202 : Nat := 118140960795 + 1840202 * 2 ^ 59
def prefixEnd_1840202 : Nat := 4983230072969 + 3 ^ 40 * 1840202 * 2
def baseEnd_1840202 : Nat := 944908127365114434912071

theorem tailTrace_1840202 : CollatzResearch.WordTrace tailWord_1840202 prefixEnd_1840202 944908127365114434912071 := by
  unfold tailWord_1840202
  simp only [CollatzResearch.WordTrace]
  refine ⟨16779420219817477581370715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44745120586179940216988573 16779420219817477581370715)
  ·
    refine ⟨25169130329726216372056073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16779420219817477581370715 25169130329726216372056073)
    ·
      refine ⟨18876847747294662279042055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25169130329726216372056073 18876847747294662279042055)
      ·
        refine ⟨28315271620941993418563083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18876847747294662279042055 28315271620941993418563083)
        ·
          refine ⟨42472907431412990127844625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28315271620941993418563083 42472907431412990127844625)
          ·
            refine ⟨31854680573559742595883469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42472907431412990127844625 31854680573559742595883469)
            ·
              refine ⟨11945505215084903473456301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31854680573559742595883469 11945505215084903473456301)
              ·
                refine ⟨4479564455656838802546113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11945505215084903473456301 4479564455656838802546113)
                ·
                  refine ⟨3359673341742629101909585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4479564455656838802546113 3359673341742629101909585)
                  ·
                    refine ⟨2519755006306971826432189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3359673341742629101909585 2519755006306971826432189)
                    ·
                      refine ⟨944908127365114434912071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2519755006306971826432189 944908127365114434912071)
                      ·
                        rfl

theorem cell23_1840202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3, 2, 2, 3].length) (baseStart_1840202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1840202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1840202 prefixEnd_1840202 := by exact prefixLift 1840202
  have htrace : WordTrace (prefixWord ++ tailWord_1840202) baseStart_1840202 baseEnd_1840202 := by
    simpa [prefixWord, tailWord_1840202, baseEnd_1840202] using wordTrace_append hprefix tailTrace_1840202
  have hstable : (prefixWord ++ tailWord_1840202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840202).length < 2 ^ (prefixWord ++ tailWord_1840202).sum := by decide
  have hdescent : baseEnd_1840202 < baseStart_1840202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840252 : List Nat := [2, 2, 2, 1, 1, 3, 2, 4, 1, 5]
def baseStart_1840252 : Nat := 118140960795 + 1840252 * 2 ^ 59
def prefixEnd_1840252 : Nat := 4983230072969 + 3 ^ 40 * 1840252 * 2
def baseEnd_1840252 : Nat := 314977933799279746428947

theorem tailTrace_1840252 : CollatzResearch.WordTrace tailWord_1840252 prefixEnd_1840252 314977933799279746428947 := by
  unfold tailWord_1840252
  simp only [CollatzResearch.WordTrace]
  refine ⟨33559752264544384432401505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44746336352725845909868673 33559752264544384432401505)
  ·
    refine ⟨25169814198408288324301129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33559752264544384432401505 25169814198408288324301129)
    ·
      refine ⟨18877360648806216243225847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25169814198408288324301129 18877360648806216243225847)
      ·
        refine ⟨28316040973209324364838771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18877360648806216243225847 28316040973209324364838771)
        ·
          refine ⟨42474061459813986547258157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28316040973209324364838771 42474061459813986547258157)
          ·
            refine ⟨15927773047430244955221809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42474061459813986547258157 15927773047430244955221809)
            ·
              refine ⟨11945829785572683716416357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15927773047430244955221809 11945829785572683716416357)
              ·
                refine ⟨2239843084794878196828067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11945829785572683716416357 2239843084794878196828067)
                ·
                  refine ⟨3359764627192317295242101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2239843084794878196828067 3359764627192317295242101)
                  ·
                    refine ⟨314977933799279746428947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3359764627192317295242101 314977933799279746428947)
                    ·
                      rfl

theorem cell23_1840252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 4, 1, 5].length) (baseStart_1840252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1840252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1840252 prefixEnd_1840252 := by exact prefixLift 1840252
  have htrace : WordTrace (prefixWord ++ tailWord_1840252) baseStart_1840252 baseEnd_1840252 := by
    simpa [prefixWord, tailWord_1840252, baseEnd_1840252] using wordTrace_append hprefix tailTrace_1840252
  have hstable : (prefixWord ++ tailWord_1840252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840252).length < 2 ^ (prefixWord ++ tailWord_1840252).sum := by decide
  have hdescent : baseEnd_1840252 < baseStart_1840252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840292 : List Nat := [2, 3, 1, 2, 3, 1, 1, 1, 3, 1, 5]
def baseStart_1840292 : Nat := 118140960795 + 1840292 * 2 ^ 59
def prefixEnd_1840292 : Nat := 4983230072969 + 3 ^ 40 * 1840292 * 2
def baseEnd_1840292 : Nat := 944954340624019082786657

theorem tailTrace_1840292 : CollatzResearch.WordTrace tailWord_1840292 prefixEnd_1840292 944954340624019082786657 := by
  unfold tailWord_1840292
  simp only [CollatzResearch.WordTrace]
  refine ⟨33560481724471927848129565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44747308965962570464172753 33560481724471927848129565)
  ·
    refine ⟨12585180646676972943048587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33560481724471927848129565 12585180646676972943048587)
    ·
      refine ⟨18877770970015459414572881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12585180646676972943048587 18877770970015459414572881)
      ·
        refine ⟨14158328227511594560929661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18877770970015459414572881 14158328227511594560929661)
        ·
          refine ⟨5309373085316847960348623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14158328227511594560929661 5309373085316847960348623)
          ·
            refine ⟨7964059627975271940522935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5309373085316847960348623 7964059627975271940522935)
            ·
              refine ⟨11946089441962907910784403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7964059627975271940522935 11946089441962907910784403)
              ·
                refine ⟨17919134162944361866176605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11946089441962907910784403 17919134162944361866176605)
                ·
                  refine ⟨6719675311104135699816227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17919134162944361866176605 6719675311104135699816227)
                  ·
                    refine ⟨10079512966656203549724341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6719675311104135699816227 10079512966656203549724341)
                    ·
                      refine ⟨944954340624019082786657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10079512966656203549724341 944954340624019082786657)
                      ·
                        rfl

theorem cell23_1840292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_1840292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1840292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1840292 prefixEnd_1840292 := by exact prefixLift 1840292
  have htrace : WordTrace (prefixWord ++ tailWord_1840292) baseStart_1840292 baseEnd_1840292 := by
    simpa [prefixWord, tailWord_1840292, baseEnd_1840292] using wordTrace_append hprefix tailTrace_1840292
  have hstable : (prefixWord ++ tailWord_1840292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840292).length < 2 ^ (prefixWord ++ tailWord_1840292).sum := by decide
  have hdescent : baseEnd_1840292 < baseStart_1840292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840306 : List Nat := [3, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2]
def baseStart_1840306 : Nat := 118140960795 + 1840306 * 2 ^ 59
def prefixEnd_1840306 : Nat := 4983230072969 + 3 ^ 40 * 1840306 * 2
def baseEnd_1840306 : Nat := 944961529353182028011593

theorem tailTrace_1840306 : CollatzResearch.WordTrace tailWord_1840306 prefixEnd_1840306 944961529353182028011593 := by
  unfold tailWord_1840306
  simp only [CollatzResearch.WordTrace]
  refine ⟨16780368517723284021817193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44747649380595424058179181 16780368517723284021817193)
  ·
    refine ⟨12585276388292463016362895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16780368517723284021817193 12585276388292463016362895)
    ·
      refine ⟨18877914582438694524544343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12585276388292463016362895 18877914582438694524544343)
      ·
        refine ⟨28316871873658041786816515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18877914582438694524544343 28316871873658041786816515)
        ·
          refine ⟨42475307810487062680224773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28316871873658041786816515 42475307810487062680224773)
          ·
            refine ⟨7964120214466324252542145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42475307810487062680224773 7964120214466324252542145)
            ·
              refine ⟨5973090160849743189406609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7964120214466324252542145 5973090160849743189406609)
              ·
                refine ⟨4479817620637307392054957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5973090160849743189406609 4479817620637307392054957)
                ·
                  refine ⟨1679931607738990272020609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4479817620637307392054957 1679931607738990272020609)
                  ·
                    refine ⟨1259948705804242704015457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1679931607738990272020609 1259948705804242704015457)
                    ·
                      refine ⟨944961529353182028011593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1259948705804242704015457 944961529353182028011593)
                      ·
                        rfl

theorem cell23_1840306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2].length) (baseStart_1840306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1840306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1840306 prefixEnd_1840306 := by exact prefixLift 1840306
  have htrace : WordTrace (prefixWord ++ tailWord_1840306) baseStart_1840306 baseEnd_1840306 := by
    simpa [prefixWord, tailWord_1840306, baseEnd_1840306] using wordTrace_append hprefix tailTrace_1840306
  have hstable : (prefixWord ++ tailWord_1840306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840306).length < 2 ^ (prefixWord ++ tailWord_1840306).sum := by decide
  have hdescent : baseEnd_1840306 < baseStart_1840306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840325 : List Nat := [1, 3, 1, 1, 1, 1, 3, 2, 1, 9]
def baseStart_1840325 : Nat := 118140960795 + 1840325 * 2 ^ 59
def prefixEnd_1840325 : Nat := 4983230072969 + 3 ^ 40 * 1840325 * 2
def baseEnd_1840325 : Nat := 314990428495205817891335

theorem tailTrace_1840325 : CollatzResearch.WordTrace tailWord_1840325 prefixEnd_1840325 314990428495205817891335 := by
  unfold tailWord_1840325
  simp only [CollatzResearch.WordTrace]
  refine ⟨67122167057824302332210429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44748111371882868221473619 67122167057824302332210429)
  ·
    refine ⟨25170812646684113374578911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67122167057824302332210429 25170812646684113374578911)
    ·
      refine ⟨37756218970026170061868367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25170812646684113374578911 37756218970026170061868367)
      ·
        refine ⟨56634328455039255092802551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37756218970026170061868367 56634328455039255092802551)
        ·
          refine ⟨84951492682558882639203827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56634328455039255092802551 84951492682558882639203827)
          ·
            refine ⟨127427239023838323958805741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84951492682558882639203827 127427239023838323958805741)
            ·
              refine ⟨47785214633939371484552153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127427239023838323958805741 47785214633939371484552153)
              ·
                refine ⟨35838910975454528613414115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47785214633939371484552153 35838910975454528613414115)
                ·
                  refine ⟨53758366463181792920121173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35838910975454528613414115 53758366463181792920121173)
                  ·
                    refine ⟨314990428495205817891335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 53758366463181792920121173 314990428495205817891335)
                    ·
                      rfl

theorem cell23_1840325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 9].length) (baseStart_1840325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1840325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1840325 prefixEnd_1840325 := by exact prefixLift 1840325
  have htrace : WordTrace (prefixWord ++ tailWord_1840325) baseStart_1840325 baseEnd_1840325 := by
    simpa [prefixWord, tailWord_1840325, baseEnd_1840325] using wordTrace_append hprefix tailTrace_1840325
  have hstable : (prefixWord ++ tailWord_1840325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840325).length < 2 ^ (prefixWord ++ tailWord_1840325).sum := by decide
  have hdescent : baseEnd_1840325 < baseStart_1840325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840383 : List Nat := [1, 1, 2, 2, 1, 6, 3, 1, 1, 3, 2]
def baseStart_1840383 : Nat := 118140960795 + 1840383 * 2 ^ 59
def prefixEnd_1840383 : Nat := 4983230072969 + 3 ^ 40 * 1840383 * 2
def baseEnd_1840383 : Nat := 945001067363578226748739

theorem tailTrace_1840383 : CollatzResearch.WordTrace tailWord_1840383 prefixEnd_1840383 945001067363578226748739 := by
  unfold tailWord_1840383
  simp only [CollatzResearch.WordTrace]
  refine ⟨67124282491614178237821803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44749521661076118825214535 67124282491614178237821803)
  ·
    refine ⟨100686423737421267356732705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67124282491614178237821803 100686423737421267356732705)
    ·
      refine ⟨75514817803065950517549529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100686423737421267356732705 75514817803065950517549529)
      ·
        refine ⟨56636113352299462888162147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75514817803065950517549529 56636113352299462888162147)
        ·
          refine ⟨84954170028449194332243221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56636113352299462888162147 84954170028449194332243221)
          ·
            refine ⟨3982226720083555984323901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 84954170028449194332243221 3982226720083555984323901)
            ·
              refine ⟨1493335020031333494121463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3982226720083555984323901 1493335020031333494121463)
              ·
                refine ⟨2240002530047000241182195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1493335020031333494121463 2240002530047000241182195)
                ·
                  refine ⟨3360003795070500361773293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2240002530047000241182195 3360003795070500361773293)
                  ·
                    refine ⟨1260001423151437635664985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3360003795070500361773293 1260001423151437635664985)
                    ·
                      refine ⟨945001067363578226748739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1260001423151437635664985 945001067363578226748739)
                      ·
                        rfl

theorem cell23_1840383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 1, 1, 3, 2].length) (baseStart_1840383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1840383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1840383 prefixEnd_1840383 := by exact prefixLift 1840383
  have htrace : WordTrace (prefixWord ++ tailWord_1840383) baseStart_1840383 baseEnd_1840383 := by
    simpa [prefixWord, tailWord_1840383, baseEnd_1840383] using wordTrace_append hprefix tailTrace_1840383
  have hstable : (prefixWord ++ tailWord_1840383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840383).length < 2 ^ (prefixWord ++ tailWord_1840383).sum := by decide
  have hdescent : baseEnd_1840383 < baseStart_1840383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840413 : List Nat := [1, 4, 2, 3, 1, 2, 2, 1, 1, 4, 2]
def baseStart_1840413 : Nat := 118140960795 + 1840413 * 2 ^ 59
def prefixEnd_1840413 : Nat := 4983230072969 + 3 ^ 40 * 1840413 * 2
def baseEnd_1840413 : Nat := 945016471783213109373601

theorem tailTrace_1840413 : CollatzResearch.WordTrace tailWord_1840413 prefixEnd_1840413 945016471783213109373601 := by
  unfold tailWord_1840413
  simp only [CollatzResearch.WordTrace]
  refine ⟨67125376681505493361413893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44750251121003662240942595 67125376681505493361413893)
  ·
    refine ⟨12586008127782280005265105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67125376681505493361413893 12586008127782280005265105)
    ·
      refine ⟨9439506095836710003948829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12586008127782280005265105 9439506095836710003948829)
      ·
        refine ⟨3539814785938766251480811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9439506095836710003948829 3539814785938766251480811)
        ·
          refine ⟨5309722178908149377221217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3539814785938766251480811 5309722178908149377221217)
          ·
            refine ⟨3982291634181112032915913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5309722178908149377221217 3982291634181112032915913)
            ·
              refine ⟨2986718725635834024686935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3982291634181112032915913 2986718725635834024686935)
              ·
                refine ⟨4480078088453751037030403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2986718725635834024686935 4480078088453751037030403)
                ·
                  refine ⟨6720117132680626555545605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4480078088453751037030403 6720117132680626555545605)
                  ·
                    refine ⟨1260021962377617479164801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6720117132680626555545605 1260021962377617479164801)
                    ·
                      refine ⟨945016471783213109373601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1260021962377617479164801 945016471783213109373601)
                      ·
                        rfl

theorem cell23_1840413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_1840413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1840413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1840413 prefixEnd_1840413 := by exact prefixLift 1840413
  have htrace : WordTrace (prefixWord ++ tailWord_1840413) baseStart_1840413 baseEnd_1840413 := by
    simpa [prefixWord, tailWord_1840413, baseEnd_1840413] using wordTrace_append hprefix tailTrace_1840413
  have hstable : (prefixWord ++ tailWord_1840413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840413).length < 2 ^ (prefixWord ++ tailWord_1840413).sum := by decide
  have hdescent : baseEnd_1840413 < baseStart_1840413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840432 : List Nat := [2, 1, 1, 1, 2, 2, 5, 1, 1, 7]
def baseStart_1840432 : Nat := 118140960795 + 1840432 * 2 ^ 59
def prefixEnd_1840432 : Nat := 4983230072969 + 3 ^ 40 * 1840432 * 2
def baseEnd_1840432 : Nat := 315008742638549511678671

theorem tailTrace_1840432 : CollatzResearch.WordTrace tailWord_1840432 prefixEnd_1840432 315008742638549511678671 := by
  unfold tailWord_1840432
  simp only [CollatzResearch.WordTrace]
  refine ⟨33563034834218329803177775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44750713112291106404237033 33563034834218329803177775)
  ·
    refine ⟨50344552251327494704766663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33563034834218329803177775 50344552251327494704766663)
    ·
      refine ⟨75516828376991242057149995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50344552251327494704766663 75516828376991242057149995)
      ·
        refine ⟨113275242565486863085724993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75516828376991242057149995 113275242565486863085724993)
        ·
          refine ⟨84956431924115147314293745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113275242565486863085724993 84956431924115147314293745)
          ·
            refine ⟨63717323943086360485720309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84956431924115147314293745 63717323943086360485720309)
            ·
              refine ⟨5973499119664346295536279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63717323943086360485720309 5973499119664346295536279)
              ·
                refine ⟨8960248679496519443304419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5973499119664346295536279 8960248679496519443304419)
                ·
                  refine ⟨13440373019244779164956629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8960248679496519443304419 13440373019244779164956629)
                  ·
                    refine ⟨315008742638549511678671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13440373019244779164956629 315008742638549511678671)
                    ·
                      rfl

theorem cell23_1840432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 1, 7].length) (baseStart_1840432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1840432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1840432 prefixEnd_1840432 := by exact prefixLift 1840432
  have htrace : WordTrace (prefixWord ++ tailWord_1840432) baseStart_1840432 baseEnd_1840432 := by
    simpa [prefixWord, tailWord_1840432, baseEnd_1840432] using wordTrace_append hprefix tailTrace_1840432
  have hstable : (prefixWord ++ tailWord_1840432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840432).length < 2 ^ (prefixWord ++ tailWord_1840432).sum := by decide
  have hdescent : baseEnd_1840432 < baseStart_1840432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840469 : List Nat := [1, 3, 2, 2, 3, 1, 1, 2, 1, 3, 4]
def baseStart_1840469 : Nat := 118140960795 + 1840469 * 2 ^ 59
def prefixEnd_1840469 : Nat := 4983230072969 + 3 ^ 40 * 1840469 * 2
def baseEnd_1840469 : Nat := 945045226699864890273343

theorem tailTrace_1840469 : CollatzResearch.WordTrace tailWord_1840469 prefixEnd_1840469 945045226699864890273343 := by
  unfold tailWord_1840469
  simp only [CollatzResearch.WordTrace]
  refine ⟨67127419169302614925452461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44751612779535076616968307 67127419169302614925452461)
  ·
    refine ⟨25172782188488480597044673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67127419169302614925452461 25172782188488480597044673)
    ·
      refine ⟨18879586641366360447783505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25172782188488480597044673 18879586641366360447783505)
      ·
        refine ⟨14159689981024770335837629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18879586641366360447783505 14159689981024770335837629)
        ·
          refine ⟨5309883742884288875939111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14159689981024770335837629 5309883742884288875939111)
          ·
            refine ⟨7964825614326433313908667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5309883742884288875939111 7964825614326433313908667)
            ·
              refine ⟨11947238421489649970863001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7964825614326433313908667 11947238421489649970863001)
              ·
                refine ⟨8960428816117237478147251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11947238421489649970863001 8960428816117237478147251)
                ·
                  refine ⟨13440643224175856217220877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8960428816117237478147251 13440643224175856217220877)
                  ·
                    refine ⟨5040241209065946081457829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13440643224175856217220877 5040241209065946081457829)
                    ·
                      refine ⟨945045226699864890273343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5040241209065946081457829 945045226699864890273343)
                      ·
                        rfl

theorem cell23_1840469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_1840469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1840469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1840469 prefixEnd_1840469 := by exact prefixLift 1840469
  have htrace : WordTrace (prefixWord ++ tailWord_1840469) baseStart_1840469 baseEnd_1840469 := by
    simpa [prefixWord, tailWord_1840469, baseEnd_1840469] using wordTrace_append hprefix tailTrace_1840469
  have hstable : (prefixWord ++ tailWord_1840469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840469).length < 2 ^ (prefixWord ++ tailWord_1840469).sum := by decide
  have hdescent : baseEnd_1840469 < baseStart_1840469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840509 : List Nat := [1, 4, 1, 1, 2, 2, 2, 4, 6]
def baseStart_1840509 : Nat := 118140960795 + 1840509 * 2 ^ 59
def prefixEnd_1840509 : Nat := 4983230072969 + 3 ^ 40 * 1840509 * 2
def baseEnd_1840509 : Nat := 105007307325116081530351

theorem tailTrace_1840509 : CollatzResearch.WordTrace tailWord_1840509 prefixEnd_1840509 105007307325116081530351 := by
  unfold tailWord_1840509
  simp only [CollatzResearch.WordTrace]
  refine ⟨67128878089157701756908581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44752585392771801171272387 67128878089157701756908581)
  ·
    refine ⟨12586664641717069079420359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67128878089157701756908581 12586664641717069079420359)
    ·
      refine ⟨18879996962575603619130539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12586664641717069079420359 18879996962575603619130539)
      ·
        refine ⟨28319995443863405428695809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18879996962575603619130539 28319995443863405428695809)
        ·
          refine ⟨21239996582897554071521857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28319995443863405428695809 21239996582897554071521857)
          ·
            refine ⟨15929997437173165553641393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21239996582897554071521857 15929997437173165553641393)
            ·
              refine ⟨11947498077879874165231045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15929997437173165553641393 11947498077879874165231045)
              ·
                refine ⟨2240155889602476405980821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11947498077879874165231045 2240155889602476405980821)
                ·
                  refine ⟨105007307325116081530351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2240155889602476405980821 105007307325116081530351)
                  ·
                    rfl

theorem cell23_1840509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 4, 6].length) (baseStart_1840509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1840509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1840509 prefixEnd_1840509 := by exact prefixLift 1840509
  have htrace : WordTrace (prefixWord ++ tailWord_1840509) baseStart_1840509 baseEnd_1840509 := by
    simpa [prefixWord, tailWord_1840509, baseEnd_1840509] using wordTrace_append hprefix tailTrace_1840509
  have hstable : (prefixWord ++ tailWord_1840509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840509).length < 2 ^ (prefixWord ++ tailWord_1840509).sum := by decide
  have hdescent : baseEnd_1840509 < baseStart_1840509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840512 : List Nat := [2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 8]
def baseStart_1840512 : Nat := 118140960795 + 1840512 * 2 ^ 59
def prefixEnd_1840512 : Nat := 4983230072969 + 3 ^ 40 * 1840512 * 2
def baseEnd_1840512 : Nat := 945067306368008222035645

theorem tailTrace_1840512 : CollatzResearch.WordTrace tailWord_1840512 prefixEnd_1840512 945067306368008222035645 := by
  unfold tailWord_1840512
  simp only [CollatzResearch.WordTrace]
  refine ⟨33564493754073416634633895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44752658338764555512845193 33564493754073416634633895)
  ·
    refine ⟨50346740631110124951950843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33564493754073416634633895 50346740631110124951950843)
    ·
      refine ⟨75520110946665187427926265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50346740631110124951950843 75520110946665187427926265)
      ·
        refine ⟨56640083209998890570944699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75520110946665187427926265 56640083209998890570944699)
        ·
          refine ⟨84960124814998335856417049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56640083209998890570944699 84960124814998335856417049)
          ·
            refine ⟨63720093611248751892312787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84960124814998335856417049 63720093611248751892312787)
            ·
              refine ⟨95580140416873127838469181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63720093611248751892312787 95580140416873127838469181)
              ·
                refine ⟨35842552656327422939425943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95580140416873127838469181 35842552656327422939425943)
                ·
                  refine ⟨53763828984491134409138915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35842552656327422939425943 53763828984491134409138915)
                  ·
                    refine ⟨80645743476736701613708373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53763828984491134409138915 80645743476736701613708373)
                    ·
                      refine ⟨945067306368008222035645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 80645743476736701613708373 945067306368008222035645)
                      ·
                        rfl

theorem cell23_1840512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 8].length) (baseStart_1840512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1840512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1840512 prefixEnd_1840512 := by exact prefixLift 1840512
  have htrace : WordTrace (prefixWord ++ tailWord_1840512) baseStart_1840512 baseEnd_1840512 := by
    simpa [prefixWord, tailWord_1840512, baseEnd_1840512] using wordTrace_append hprefix tailTrace_1840512
  have hstable : (prefixWord ++ tailWord_1840512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840512).length < 2 ^ (prefixWord ++ tailWord_1840512).sum := by decide
  have hdescent : baseEnd_1840512 < baseStart_1840512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840540 : List Nat := [2, 2, 3, 4, 1, 1, 2, 1, 2, 2, 3]
def baseStart_1840540 : Nat := 118140960795 + 1840540 * 2 ^ 59
def prefixEnd_1840540 : Nat := 4983230072969 + 3 ^ 40 * 1840540 * 2
def baseEnd_1840540 : Nat := 945081683826334112485517

theorem tailTrace_1840540 : CollatzResearch.WordTrace tailWord_1840540 prefixEnd_1840540 945081683826334112485517 := by
  unfold tailWord_1840540
  simp only [CollatzResearch.WordTrace]
  refine ⟨33565004376022697025643537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44753339168030262700858049 33565004376022697025643537)
  ·
    refine ⟨25173753282017022769232653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33565004376022697025643537 25173753282017022769232653)
    ·
      refine ⟨9440157480756383538462245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25173753282017022769232653 9440157480756383538462245)
      ·
        refine ⟨1770029527641821913461671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9440157480756383538462245 1770029527641821913461671)
        ·
          refine ⟨2655044291462732870192507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1770029527641821913461671 2655044291462732870192507)
          ·
            refine ⟨3982566437194099305288761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2655044291462732870192507 3982566437194099305288761)
            ·
              refine ⟨2986924827895574478966571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3982566437194099305288761 2986924827895574478966571)
              ·
                refine ⟨4480387241843361718449857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2986924827895574478966571 4480387241843361718449857)
                ·
                  refine ⟨3360290431382521288837393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4480387241843361718449857 3360290431382521288837393)
                  ·
                    refine ⟨2520217823536890966628045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3360290431382521288837393 2520217823536890966628045)
                    ·
                      refine ⟨945081683826334112485517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2520217823536890966628045 945081683826334112485517)
                      ·
                        rfl

theorem cell23_1840540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_1840540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1840540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1840540 prefixEnd_1840540 := by exact prefixLift 1840540
  have htrace : WordTrace (prefixWord ++ tailWord_1840540) baseStart_1840540 baseEnd_1840540 := by
    simpa [prefixWord, tailWord_1840540, baseEnd_1840540] using wordTrace_append hprefix tailTrace_1840540
  have hstable : (prefixWord ++ tailWord_1840540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840540).length < 2 ^ (prefixWord ++ tailWord_1840540).sum := by decide
  have hdescent : baseEnd_1840540 < baseStart_1840540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840579 : List Nat := [1, 1, 1, 3, 1, 1, 4, 4, 1, 1, 5]
def baseStart_1840579 : Nat := 118140960795 + 1840579 * 2 ^ 59
def prefixEnd_1840579 : Nat := 4983230072969 + 3 ^ 40 * 1840579 * 2
def baseEnd_1840579 : Nat := 945101709571859459897837

theorem tailTrace_1840579 : CollatzResearch.WordTrace tailWord_1840579 prefixEnd_1840579 945101709571859459897837 := by
  unfold tailWord_1840579
  simp only [CollatzResearch.WordTrace]
  refine ⟨67131431198904103711956791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44754287465936069141304527 67131431198904103711956791)
  ·
    refine ⟨100697146798356155567935187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67131431198904103711956791 100697146798356155567935187)
    ·
      refine ⟨151045720197534233351902781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100697146798356155567935187 151045720197534233351902781)
      ·
        refine ⟨56642145074075337506963543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151045720197534233351902781 56642145074075337506963543)
        ·
          refine ⟨84963217611113006260445315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56642145074075337506963543 84963217611113006260445315)
          ·
            refine ⟨127444826416669509390667973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84963217611113006260445315 127444826416669509390667973)
            ·
              refine ⟨23895904953125533010750245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127444826416669509390667973 23895904953125533010750245)
              ·
                refine ⟨4480482178711037439515671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23895904953125533010750245 4480482178711037439515671)
                ·
                  refine ⟨6720723268066556159273507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4480482178711037439515671 6720723268066556159273507)
                  ·
                    refine ⟨10081084902099834238910261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6720723268066556159273507 10081084902099834238910261)
                    ·
                      refine ⟨945101709571859459897837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10081084902099834238910261 945101709571859459897837)
                      ·
                        rfl

theorem cell23_1840579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4, 1, 1, 5].length) (baseStart_1840579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1840579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1840579 prefixEnd_1840579 := by exact prefixLift 1840579
  have htrace : WordTrace (prefixWord ++ tailWord_1840579) baseStart_1840579 baseEnd_1840579 := by
    simpa [prefixWord, tailWord_1840579, baseEnd_1840579] using wordTrace_append hprefix tailTrace_1840579
  have hstable : (prefixWord ++ tailWord_1840579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840579).length < 2 ^ (prefixWord ++ tailWord_1840579).sum := by decide
  have hdescent : baseEnd_1840579 < baseStart_1840579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840586 : List Nat := [3, 1, 2, 1, 2, 4, 2, 1, 1, 6]
def baseStart_1840586 : Nat := 118140960795 + 1840586 * 2 ^ 59
def prefixEnd_1840586 : Nat := 4983230072969 + 3 ^ 40 * 1840586 * 2
def baseEnd_1840586 : Nat := 315035101312146977503435

theorem tailTrace_1840586 : CollatzResearch.WordTrace tailWord_1840586 prefixEnd_1840586 315035101312146977503435 := by
  unfold tailWord_1840586
  simp only [CollatzResearch.WordTrace]
  refine ⟨16782921627469685976865403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44754457673252495938307741 16782921627469685976865403)
  ·
    refine ⟨25174382441204528965298105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16782921627469685976865403 25174382441204528965298105)
    ·
      refine ⟨18880786830903396723973579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25174382441204528965298105 18880786830903396723973579)
      ·
        refine ⟨28321180246355095085960369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18880786830903396723973579 28321180246355095085960369)
        ·
          refine ⟨21240885184766321314470277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28321180246355095085960369 21240885184766321314470277)
          ·
            refine ⟨3982665972143685246463177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21240885184766321314470277 3982665972143685246463177)
            ·
              refine ⟨2986999479107763934847383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3982665972143685246463177 2986999479107763934847383)
              ·
                refine ⟨4480499218661645902271075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2986999479107763934847383 4480499218661645902271075)
                ·
                  refine ⟨6720748827992468853406613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4480499218661645902271075 6720748827992468853406613)
                  ·
                    refine ⟨315035101312146977503435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6720748827992468853406613 315035101312146977503435)
                    ·
                      rfl

theorem cell23_1840586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 1, 1, 6].length) (baseStart_1840586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1840586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1840586 prefixEnd_1840586 := by exact prefixLift 1840586
  have htrace : WordTrace (prefixWord ++ tailWord_1840586) baseStart_1840586 baseEnd_1840586 := by
    simpa [prefixWord, tailWord_1840586, baseEnd_1840586] using wordTrace_append hprefix tailTrace_1840586
  have hstable : (prefixWord ++ tailWord_1840586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840586).length < 2 ^ (prefixWord ++ tailWord_1840586).sum := by decide
  have hdescent : baseEnd_1840586 < baseStart_1840586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840717 : List Nat := [1, 6, 1, 1, 3, 1, 1, 2, 1, 4, 2]
def baseStart_1840717 : Nat := 118140960795 + 1840717 * 2 ^ 59
def prefixEnd_1840717 : Nat := 4983230072969 + 3 ^ 40 * 1840717 * 2
def baseEnd_1840717 : Nat := 945172569902179919972203

theorem tailTrace_1840717 : CollatzResearch.WordTrace tailWord_1840717 prefixEnd_1840717 945172569902179919972203 := by
  unfold tailWord_1840717
  simp only [CollatzResearch.WordTrace]
  refine ⟨67136464472404153280480405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44757642981602768853653603 67136464472404153280480405)
  ·
    refine ⟨3147021772143944685022519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 67136464472404153280480405 3147021772143944685022519)
    ·
      refine ⟨4720532658215917027533779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3147021772143944685022519 4720532658215917027533779)
      ·
        refine ⟨7080798987323875541300669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4720532658215917027533779 7080798987323875541300669)
        ·
          refine ⟨2655299620246453327987751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7080798987323875541300669 2655299620246453327987751)
          ·
            refine ⟨3982949430369679991981627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2655299620246453327987751 3982949430369679991981627)
            ·
              refine ⟨5974424145554519987972441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3982949430369679991981627 5974424145554519987972441)
              ·
                refine ⟨4480818109165889990979331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5974424145554519987972441 4480818109165889990979331)
                ·
                  refine ⟨6721227163748834986468997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4480818109165889990979331 6721227163748834986468997)
                  ·
                    refine ⟨1260230093202906559962937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6721227163748834986468997 1260230093202906559962937)
                    ·
                      refine ⟨945172569902179919972203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1260230093202906559962937 945172569902179919972203)
                      ·
                        rfl

theorem cell23_1840717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_1840717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1840717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1840717 prefixEnd_1840717 := by exact prefixLift 1840717
  have htrace : WordTrace (prefixWord ++ tailWord_1840717) baseStart_1840717 baseEnd_1840717 := by
    simpa [prefixWord, tailWord_1840717, baseEnd_1840717] using wordTrace_append hprefix tailTrace_1840717
  have hstable : (prefixWord ++ tailWord_1840717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840717).length < 2 ^ (prefixWord ++ tailWord_1840717).sum := by decide
  have hdescent : baseEnd_1840717 < baseStart_1840717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840740 : List Nat := [2, 3, 1, 1, 2, 3, 4, 2, 5]
def baseStart_1840740 : Nat := 118140960795 + 1840740 * 2 ^ 59
def prefixEnd_1840740 : Nat := 4983230072969 + 3 ^ 40 * 1840740 * 2
def baseEnd_1840740 : Nat := 105020486661914814442733

theorem tailTrace_1840740 : CollatzResearch.WordTrace tailWord_1840740 prefixEnd_1840740 105020486661914814442733 := by
  unfold tailWord_1840740
  simp only [CollatzResearch.WordTrace]
  refine ⟨33568651675660414104283837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44758202234213885472378449 33568651675660414104283837)
  ·
    refine ⟨12588244378372655289106439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33568651675660414104283837 12588244378372655289106439)
    ·
      refine ⟨18882366567558982933659659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12588244378372655289106439 18882366567558982933659659)
      ·
        refine ⟨28323549851338474400489489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18882366567558982933659659 28323549851338474400489489)
        ·
          refine ⟨21242662388503855800367117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28323549851338474400489489 21242662388503855800367117)
          ·
            refine ⟨7965998395688945925137669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21242662388503855800367117 7965998395688945925137669)
            ·
              refine ⟨1493624699191677360963313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7965998395688945925137669 1493624699191677360963313)
              ·
                refine ⟨1120218524393758020722485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1493624699191677360963313 1120218524393758020722485)
                ·
                  refine ⟨105020486661914814442733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1120218524393758020722485 105020486661914814442733)
                  ·
                    rfl

theorem cell23_1840740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 2, 5].length) (baseStart_1840740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1840740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1840740 prefixEnd_1840740 := by exact prefixLift 1840740
  have htrace : WordTrace (prefixWord ++ tailWord_1840740) baseStart_1840740 baseEnd_1840740 := by
    simpa [prefixWord, tailWord_1840740, baseEnd_1840740] using wordTrace_append hprefix tailTrace_1840740
  have hstable : (prefixWord ++ tailWord_1840740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840740).length < 2 ^ (prefixWord ++ tailWord_1840740).sum := by decide
  have hdescent : baseEnd_1840740 < baseStart_1840740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840743 : List Nat := [1, 1, 5, 1, 1, 1, 3, 1, 2, 5, 2]
def baseStart_1840743 : Nat := 118140960795 + 1840743 * 2 ^ 59
def prefixEnd_1840743 : Nat := 4983230072969 + 3 ^ 40 * 1840743 * 2
def baseEnd_1840743 : Nat := 945185920399196818247083

theorem tailTrace_1840743 : CollatzResearch.WordTrace tailWord_1840743 prefixEnd_1840743 945185920399196818247083 := by
  unfold tailWord_1840743
  simp only [CollatzResearch.WordTrace]
  refine ⟨67137412770309959720926883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44758275180206639813951255 67137412770309959720926883)
  ·
    refine ⟨100706119155464939581390325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67137412770309959720926883 100706119155464939581390325)
    ·
      refine ⟨9441198670824838085755343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100706119155464939581390325 9441198670824838085755343)
      ·
        refine ⟨14161798006237257128633015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9441198670824838085755343 14161798006237257128633015)
        ·
          refine ⟨21242697009355885692949523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14161798006237257128633015 21242697009355885692949523)
          ·
            refine ⟨31864045514033828539424285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21242697009355885692949523 31864045514033828539424285)
            ·
              refine ⟨11949017067762685702284107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31864045514033828539424285 11949017067762685702284107)
              ·
                refine ⟨17923525601644028553426161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11949017067762685702284107 17923525601644028553426161)
                ·
                  refine ⟨13442644201233021415069621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17923525601644028553426161 13442644201233021415069621)
                  ·
                    refine ⟨1260247893865595757662777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13442644201233021415069621 1260247893865595757662777)
                    ·
                      refine ⟨945185920399196818247083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1260247893865595757662777 945185920399196818247083)
                      ·
                        rfl

theorem cell23_1840743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 5, 2].length) (baseStart_1840743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1840743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1840743 prefixEnd_1840743 := by exact prefixLift 1840743
  have htrace : WordTrace (prefixWord ++ tailWord_1840743) baseStart_1840743 baseEnd_1840743 := by
    simpa [prefixWord, tailWord_1840743, baseEnd_1840743] using wordTrace_append hprefix tailTrace_1840743
  have hstable : (prefixWord ++ tailWord_1840743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840743).length < 2 ^ (prefixWord ++ tailWord_1840743).sum := by decide
  have hdescent : baseEnd_1840743 < baseStart_1840743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840750 : List Nat := [4, 1, 2, 2, 3, 1, 1, 1, 2, 3, 3]
def baseStart_1840750 : Nat := 118140960795 + 1840750 * 2 ^ 59
def prefixEnd_1840750 : Nat := 4983230072969 + 3 ^ 40 * 1840750 * 2
def baseEnd_1840750 : Nat := 945189514763778290859551

theorem tailTrace_1840750 : CollatzResearch.WordTrace tailWord_1840750 prefixEnd_1840750 945189514763778290859551 := by
  unfold tailWord_1840750
  simp only [CollatzResearch.WordTrace]
  refine ⟨8392208510160574989553963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44758445387523066610954469 8392208510160574989553963)
  ·
    refine ⟨12588312765240862484330945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8392208510160574989553963 12588312765240862484330945)
    ·
      refine ⟨9441234573930646863248209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12588312765240862484330945 9441234573930646863248209)
      ·
        refine ⟨7080925930447985147436157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9441234573930646863248209 7080925930447985147436157)
        ·
          refine ⟨2655347223917994430288559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7080925930447985147436157 2655347223917994430288559)
          ·
            refine ⟨3983020835876991645432839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2655347223917994430288559 3983020835876991645432839)
            ·
              refine ⟨5974531253815487468149259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3983020835876991645432839 5974531253815487468149259)
              ·
                refine ⟨8961796880723231202223889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5974531253815487468149259 8961796880723231202223889)
                ·
                  refine ⟨6721347660542423401667917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8961796880723231202223889 6721347660542423401667917)
                  ·
                    refine ⟨2520505372703408775625469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6721347660542423401667917 2520505372703408775625469)
                    ·
                      refine ⟨945189514763778290859551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2520505372703408775625469 945189514763778290859551)
                      ·
                        rfl

theorem cell23_1840750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_1840750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1840750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1840750 prefixEnd_1840750 := by exact prefixLift 1840750
  have htrace : WordTrace (prefixWord ++ tailWord_1840750) baseStart_1840750 baseEnd_1840750 := by
    simpa [prefixWord, tailWord_1840750, baseEnd_1840750] using wordTrace_append hprefix tailTrace_1840750
  have hstable : (prefixWord ++ tailWord_1840750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840750).length < 2 ^ (prefixWord ++ tailWord_1840750).sum := by decide
  have hdescent : baseEnd_1840750 < baseStart_1840750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840773 : List Nat := [1, 3, 1, 1, 4, 1, 1, 2, 1, 6, 2]
def baseStart_1840773 : Nat := 118140960795 + 1840773 * 2 ^ 59
def prefixEnd_1840773 : Nat := 4983230072969 + 3 ^ 40 * 1840773 * 2
def baseEnd_1840773 : Nat := 945201324818831700871945

theorem tailTrace_1840773 : CollatzResearch.WordTrace tailWord_1840773 prefixEnd_1840773 945201324818831700871945 := by
  unfold tailWord_1840773
  simp only [CollatzResearch.WordTrace]
  refine ⟨67138506960201274844518973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44759004640134183229679315 67138506960201274844518973)
  ·
    refine ⟨25176940110075478066694615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67138506960201274844518973 25176940110075478066694615)
    ·
      refine ⟨37765410165113217100041923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25176940110075478066694615 37765410165113217100041923)
      ·
        refine ⟨56648115247669825650062885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37765410165113217100041923 56648115247669825650062885)
        ·
          refine ⟨10621521608938092309386791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56648115247669825650062885 10621521608938092309386791)
          ·
            refine ⟨15932282413407138464080187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10621521608938092309386791 15932282413407138464080187)
            ·
              refine ⟨23898423620110707696120281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15932282413407138464080187 23898423620110707696120281)
              ·
                refine ⟨17923817715083030772090211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23898423620110707696120281 17923817715083030772090211)
                ·
                  refine ⟨26885726572624546158135317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17923817715083030772090211 26885726572624546158135317)
                  ·
                    refine ⟨1260268433091775601162593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26885726572624546158135317 1260268433091775601162593)
                    ·
                      refine ⟨945201324818831700871945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1260268433091775601162593 945201324818831700871945)
                      ·
                        rfl

theorem cell23_1840773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 6, 2].length) (baseStart_1840773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1840773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1840773 prefixEnd_1840773 := by exact prefixLift 1840773
  have htrace : WordTrace (prefixWord ++ tailWord_1840773) baseStart_1840773 baseEnd_1840773 := by
    simpa [prefixWord, tailWord_1840773, baseEnd_1840773] using wordTrace_append hprefix tailTrace_1840773
  have hstable : (prefixWord ++ tailWord_1840773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840773).length < 2 ^ (prefixWord ++ tailWord_1840773).sum := by decide
  have hdescent : baseEnd_1840773 < baseStart_1840773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840800 : List Nat := [2, 1, 1, 4, 3, 2, 2, 1, 3, 4]
def baseStart_1840800 : Nat := 118140960795 + 1840800 * 2 ^ 59
def prefixEnd_1840800 : Nat := 4983230072969 + 3 ^ 40 * 1840800 * 2
def baseEnd_1840800 : Nat := 315071729598834365078107

theorem tailTrace_1840800 : CollatzResearch.WordTrace tailWord_1840800 prefixEnd_1840800 315071729598834365078107 := by
  unfold tailWord_1840800
  simp only [CollatzResearch.WordTrace]
  refine ⟨33569745865551729227875927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44759661154068972303834569 33569745865551729227875927)
  ·
    refine ⟨50354618798327593841813891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33569745865551729227875927 50354618798327593841813891)
    ·
      refine ⟨75531928197491390762720837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50354618798327593841813891 75531928197491390762720837)
      ·
        refine ⟨14162236537029635768010157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75531928197491390762720837 14162236537029635768010157)
        ·
          refine ⟨5310838701386113413003809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14162236537029635768010157 5310838701386113413003809)
          ·
            refine ⟨3983129026039585059752857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5310838701386113413003809 3983129026039585059752857)
            ·
              refine ⟨2987346769529688794814643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3983129026039585059752857 2987346769529688794814643)
              ·
                refine ⟨4481020154294533192221965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2987346769529688794814643 4481020154294533192221965)
                ·
                  refine ⟨1680382557860449947083237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4481020154294533192221965 1680382557860449947083237)
                  ·
                    refine ⟨315071729598834365078107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1680382557860449947083237 315071729598834365078107)
                    ·
                      rfl

theorem cell23_1840800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 1, 3, 4].length) (baseStart_1840800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1840800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1840800 prefixEnd_1840800 := by exact prefixLift 1840800
  have htrace : WordTrace (prefixWord ++ tailWord_1840800) baseStart_1840800 baseEnd_1840800 := by
    simpa [prefixWord, tailWord_1840800, baseEnd_1840800] using wordTrace_append hprefix tailTrace_1840800
  have hstable : (prefixWord ++ tailWord_1840800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840800).length < 2 ^ (prefixWord ++ tailWord_1840800).sum := by decide
  have hdescent : baseEnd_1840800 < baseStart_1840800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840857 : List Nat := [1, 2, 1, 2, 3, 5, 1, 1, 3, 1, 3]
def baseStart_1840857 : Nat := 118140960795 + 1840857 * 2 ^ 59
def prefixEnd_1840857 : Nat := 4983230072969 + 3 ^ 40 * 1840857 * 2
def baseEnd_1840857 : Nat := 945244457193809372221559

theorem tailTrace_1840857 : CollatzResearch.WordTrace tailWord_1840857 prefixEnd_1840857 945244457193809372221559 := by
  unfold tailWord_1840857
  simp only [CollatzResearch.WordTrace]
  refine ⟨67141570691896957190576825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44761047127931304793717883 67141570691896957190576825)
  ·
    refine ⟨50356178018922717892932619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67141570691896957190576825 50356178018922717892932619)
    ·
      refine ⟨75534267028384076839398929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50356178018922717892932619 75534267028384076839398929)
      ·
        refine ⟨56650700271288057629549197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75534267028384076839398929 56650700271288057629549197)
        ·
          refine ⟨21244012601733021611080949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56650700271288057629549197 21244012601733021611080949)
          ·
            refine ⟨1991626181412470776038839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21244012601733021611080949 1991626181412470776038839)
            ·
              refine ⟨2987439272118706164058259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1991626181412470776038839 2987439272118706164058259)
              ·
                refine ⟨4481158908178059246087389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2987439272118706164058259 4481158908178059246087389)
                ·
                  refine ⟨1680434590566772217282771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4481158908178059246087389 1680434590566772217282771)
                  ·
                    refine ⟨2520651885850158325924157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1680434590566772217282771 2520651885850158325924157)
                    ·
                      refine ⟨945244457193809372221559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2520651885850158325924157 945244457193809372221559)
                      ·
                        rfl

theorem cell23_1840857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 1, 3, 1, 3].length) (baseStart_1840857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1840857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1840857 prefixEnd_1840857 := by exact prefixLift 1840857
  have htrace : WordTrace (prefixWord ++ tailWord_1840857) baseStart_1840857 baseEnd_1840857 := by
    simpa [prefixWord, tailWord_1840857, baseEnd_1840857] using wordTrace_append hprefix tailTrace_1840857
  have hstable : (prefixWord ++ tailWord_1840857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840857).length < 2 ^ (prefixWord ++ tailWord_1840857).sum := by decide
  have hdescent : baseEnd_1840857 < baseStart_1840857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840863 : List Nat := [1, 1, 2, 3, 2, 2, 2, 2, 3, 1, 4]
def baseStart_1840863 : Nat := 118140960795 + 1840863 * 2 ^ 59
def prefixEnd_1840863 : Nat := 4983230072969 + 3 ^ 40 * 1840863 * 2
def baseEnd_1840863 : Nat := 945247538077736348746531

theorem tailTrace_1840863 : CollatzResearch.WordTrace tailWord_1840863 prefixEnd_1840863 945247538077736348746531 := by
  unfold tailWord_1840863
  simp only [CollatzResearch.WordTrace]
  refine ⟨67141789529875220215295243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44761193019916813476863495 67141789529875220215295243)
  ·
    refine ⟨100712684294812830322942865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67141789529875220215295243 100712684294812830322942865)
    ·
      refine ⟨75534513221109622742207149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100712684294812830322942865 75534513221109622742207149)
      ·
        refine ⟨28325442457916108528327681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75534513221109622742207149 28325442457916108528327681)
        ·
          refine ⟨21244081843437081396245761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28325442457916108528327681 21244081843437081396245761)
          ·
            refine ⟨15933061382577811047184321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21244081843437081396245761 15933061382577811047184321)
            ·
              refine ⟨11949796036933358285388241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15933061382577811047184321 11949796036933358285388241)
              ·
                refine ⟨8962347027700018714041181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11949796036933358285388241 8962347027700018714041181)
                ·
                  refine ⟨3360880135387507017765443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8962347027700018714041181 3360880135387507017765443)
                  ·
                    refine ⟨5041320203081260526648165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3360880135387507017765443 5041320203081260526648165)
                    ·
                      refine ⟨945247538077736348746531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5041320203081260526648165 945247538077736348746531)
                      ·
                        rfl

theorem cell23_1840863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 3, 1, 4].length) (baseStart_1840863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1840863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1840863 prefixEnd_1840863 := by exact prefixLift 1840863
  have htrace : WordTrace (prefixWord ++ tailWord_1840863) baseStart_1840863 baseEnd_1840863 := by
    simpa [prefixWord, tailWord_1840863, baseEnd_1840863] using wordTrace_append hprefix tailTrace_1840863
  have hstable : (prefixWord ++ tailWord_1840863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840863).length < 2 ^ (prefixWord ++ tailWord_1840863).sum := by decide
  have hdescent : baseEnd_1840863 < baseStart_1840863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840877 : List Nat := [1, 5, 1, 2, 1, 4, 1, 2, 1, 5]
def baseStart_1840877 : Nat := 118140960795 + 1840877 * 2 ^ 59
def prefixEnd_1840877 : Nat := 4983230072969 + 3 ^ 40 * 1840877 * 2
def baseEnd_1840877 : Nat := 315084908935633097990489

theorem tailTrace_1840877 : CollatzResearch.WordTrace tailWord_1840877 prefixEnd_1840877 315084908935633097990489 := by
  unfold tailWord_1840877
  simp only [CollatzResearch.WordTrace]
  refine ⟨67142300151824500606304885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44761533434549667070869923 67142300151824500606304885)
  ·
    refine ⟨6294590639233546931841083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67142300151824500606304885 6294590639233546931841083)
    ·
      refine ⟨9441885958850320397761625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6294590639233546931841083 9441885958850320397761625)
      ·
        refine ⟨7081414469137740298321219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9441885958850320397761625 7081414469137740298321219)
        ·
          refine ⟨10622121703706610447481829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7081414469137740298321219 10622121703706610447481829)
          ·
            refine ⟨1991647819444989458902843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10622121703706610447481829 1991647819444989458902843)
            ·
              refine ⟨2987471729167484188354265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1991647819444989458902843 2987471729167484188354265)
              ·
                refine ⟨2240603796875613141265699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2987471729167484188354265 2240603796875613141265699)
                ·
                  refine ⟨3360905695313419711898549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2240603796875613141265699 3360905695313419711898549)
                  ·
                    refine ⟨315084908935633097990489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3360905695313419711898549 315084908935633097990489)
                    ·
                      rfl

theorem cell23_1840877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_1840877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1840877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1840877 prefixEnd_1840877 := by exact prefixLift 1840877
  have htrace : WordTrace (prefixWord ++ tailWord_1840877) baseStart_1840877 baseEnd_1840877 := by
    simpa [prefixWord, tailWord_1840877, baseEnd_1840877] using wordTrace_append hprefix tailTrace_1840877
  have hstable : (prefixWord ++ tailWord_1840877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840877).length < 2 ^ (prefixWord ++ tailWord_1840877).sum := by decide
  have hdescent : baseEnd_1840877 < baseStart_1840877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840894 : List Nat := [4, 2, 2, 1, 3, 1, 3, 1, 1, 5]
def baseStart_1840894 : Nat := 118140960795 + 1840894 * 2 ^ 59
def prefixEnd_1840894 : Nat := 4983230072969 + 3 ^ 40 * 1840894 * 2
def baseEnd_1840894 : Nat := 315087818659341909152963

theorem tailTrace_1840894 : CollatzResearch.WordTrace tailWord_1840894 prefixEnd_1840894 315087818659341909152963 := by
  unfold tailWord_1840894
  simp only [CollatzResearch.WordTrace]
  refine ⟨8392865024095364063709217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44761946795175275006449157 8392865024095364063709217)
  ·
    refine ⟨6294648768071523047781913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8392865024095364063709217 6294648768071523047781913)
    ·
      refine ⟨4720986576053642285836435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6294648768071523047781913 4720986576053642285836435)
      ·
        refine ⟨7081479864080463428754653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4720986576053642285836435 7081479864080463428754653)
        ·
          refine ⟨2655554949030173785782995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7081479864080463428754653 2655554949030173785782995)
          ·
            refine ⟨3983332423545260678674493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2655554949030173785782995 3983332423545260678674493)
            ·
              refine ⟨1493749658829472754502935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3983332423545260678674493 1493749658829472754502935)
              ·
                refine ⟨2240624488244209131754403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1493749658829472754502935 2240624488244209131754403)
                ·
                  refine ⟨3360936732366313697631605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2240624488244209131754403 3360936732366313697631605)
                  ·
                    refine ⟨315087818659341909152963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3360936732366313697631605 315087818659341909152963)
                    ·
                      rfl

theorem cell23_1840894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_1840894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1840894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1840894 prefixEnd_1840894 := by exact prefixLift 1840894
  have htrace : WordTrace (prefixWord ++ tailWord_1840894) baseStart_1840894 baseEnd_1840894 := by
    simpa [prefixWord, tailWord_1840894, baseEnd_1840894] using wordTrace_append hprefix tailTrace_1840894
  have hstable : (prefixWord ++ tailWord_1840894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840894).length < 2 ^ (prefixWord ++ tailWord_1840894).sum := by decide
  have hdescent : baseEnd_1840894 < baseStart_1840894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840900 : List Nat := [2, 3, 2, 2, 1, 2, 3, 1, 1, 1, 5]
def baseStart_1840900 : Nat := 118140960795 + 1840900 * 2 ^ 59
def prefixEnd_1840900 : Nat := 4983230072969 + 3 ^ 40 * 1840900 * 2
def baseEnd_1840900 : Nat := 945266536861952703983861

theorem tailTrace_1840900 : CollatzResearch.WordTrace tailWord_1840900 prefixEnd_1840900 945266536861952703983861 := by
  unfold tailWord_1840900
  simp only [CollatzResearch.WordTrace]
  refine ⟨33571569515370587767196077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44762092687160783689594769 33571569515370587767196077)
  ·
    refine ⟨12589338568263970412698529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33571569515370587767196077 12589338568263970412698529)
    ·
      refine ⟨9442003926197977809523897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12589338568263970412698529 9442003926197977809523897)
      ·
        refine ⟨7081502944648483357142923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9442003926197977809523897 7081502944648483357142923)
        ·
          refine ⟨10622254416972725035714385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7081502944648483357142923 10622254416972725035714385)
          ·
            refine ⟨7966690812729543776785789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10622254416972725035714385 7966690812729543776785789)
            ·
              refine ⟨2987509054773578916294671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7966690812729543776785789 2987509054773578916294671)
              ·
                refine ⟨4481263582160368374442007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2987509054773578916294671 4481263582160368374442007)
                ·
                  refine ⟨6721895373240552561663011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4481263582160368374442007 6721895373240552561663011)
                  ·
                    refine ⟨10082843059860828842494517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6721895373240552561663011 10082843059860828842494517)
                    ·
                      refine ⟨945266536861952703983861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10082843059860828842494517 945266536861952703983861)
                      ·
                        rfl

theorem cell23_1840900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_1840900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1840900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1840900 prefixEnd_1840900 := by exact prefixLift 1840900
  have htrace : WordTrace (prefixWord ++ tailWord_1840900) baseStart_1840900 baseEnd_1840900 := by
    simpa [prefixWord, tailWord_1840900, baseEnd_1840900] using wordTrace_append hprefix tailTrace_1840900
  have hstable : (prefixWord ++ tailWord_1840900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840900).length < 2 ^ (prefixWord ++ tailWord_1840900).sum := by decide
  have hdescent : baseEnd_1840900 < baseStart_1840900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840903 : List Nat := [1, 1, 4, 4, 2, 11]
def baseStart_1840903 : Nat := 118140960795 + 1840903 * 2 ^ 59
def prefixEnd_1840903 : Nat := 4983230072969 + 3 ^ 40 * 1840903 * 2
def baseEnd_1840903 : Nat := 3889992087670437005129

theorem tailTrace_1840903 : CollatzResearch.WordTrace tailWord_1840903 prefixEnd_1840903 3889992087670437005129 := by
  unfold tailWord_1840903
  simp only [CollatzResearch.WordTrace]
  refine ⟨67143248449730307046751363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44762165633153538031167575 67143248449730307046751363)
  ·
    refine ⟨100714872674595460570127045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67143248449730307046751363 100714872674595460570127045)
    ·
      refine ⟨18884038626486648856898821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100714872674595460570127045 18884038626486648856898821)
      ·
        refine ⟨3540757242466246660668529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18884038626486648856898821 3540757242466246660668529)
        ·
          refine ⟨2655567931849684995501397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3540757242466246660668529 2655567931849684995501397)
          ·
            refine ⟨3889992087670437005129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2655567931849684995501397 3889992087670437005129)
            ·
              rfl

theorem cell23_1840903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 11].length) (baseStart_1840903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1840903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1840903 prefixEnd_1840903 := by exact prefixLift 1840903
  have htrace : WordTrace (prefixWord ++ tailWord_1840903) baseStart_1840903 baseEnd_1840903 := by
    simpa [prefixWord, tailWord_1840903, baseEnd_1840903] using wordTrace_append hprefix tailTrace_1840903
  have hstable : (prefixWord ++ tailWord_1840903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840903).length < 2 ^ (prefixWord ++ tailWord_1840903).sum := by decide
  have hdescent : baseEnd_1840903 < baseStart_1840903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840913 : List Nat := [1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 3]
def baseStart_1840913 : Nat := 118140960795 + 1840913 * 2 ^ 59
def prefixEnd_1840913 : Nat := 4983230072969 + 3 ^ 40 * 1840913 * 2
def baseEnd_1840913 : Nat := 945273212110461153121301

theorem tailTrace_1840913 : CollatzResearch.WordTrace tailWord_1840913 prefixEnd_1840913 945273212110461153121301 := by
  unfold tailWord_1840913
  simp only [CollatzResearch.WordTrace]
  refine ⟨67143613179694078754615393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44762408786462719169743595 67143613179694078754615393)
  ·
    refine ⟨50357709884770559065961545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67143613179694078754615393 50357709884770559065961545)
    ·
      refine ⟨37768282413577919299471159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50357709884770559065961545 37768282413577919299471159)
      ·
        refine ⟨56652423620366878949206739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37768282413577919299471159 56652423620366878949206739)
        ·
          refine ⟨84978635430550318423810109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56652423620366878949206739 84978635430550318423810109)
          ·
            refine ⟨31866988286456369408928791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84978635430550318423810109 31866988286456369408928791)
            ·
              refine ⟨47800482429684554113393187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31866988286456369408928791 47800482429684554113393187)
              ·
                refine ⟨71700723644526831170089781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47800482429684554113393187 71700723644526831170089781)
                ·
                  refine ⟨6721942841674390422195917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71700723644526831170089781 6721942841674390422195917)
                  ·
                    refine ⟨2520728565627896408323469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6721942841674390422195917 2520728565627896408323469)
                    ·
                      refine ⟨945273212110461153121301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2520728565627896408323469 945273212110461153121301)
                      ·
                        rfl

theorem cell23_1840913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 3].length) (baseStart_1840913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1840913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1840913 prefixEnd_1840913 := by exact prefixLift 1840913
  have htrace : WordTrace (prefixWord ++ tailWord_1840913) baseStart_1840913 baseEnd_1840913 := by
    simpa [prefixWord, tailWord_1840913, baseEnd_1840913] using wordTrace_append hprefix tailTrace_1840913
  have hstable : (prefixWord ++ tailWord_1840913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840913).length < 2 ^ (prefixWord ++ tailWord_1840913).sum := by decide
  have hdescent : baseEnd_1840913 < baseStart_1840913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840948 : List Nat := [2, 5, 1, 1, 2, 2, 2, 3, 1, 2, 2]
def baseStart_1840948 : Nat := 118140960795 + 1840948 * 2 ^ 59
def prefixEnd_1840948 : Nat := 4983230072969 + 3 ^ 40 * 1840948 * 2
def baseEnd_1840948 : Nat := 945291183933368516183641

theorem tailTrace_1840948 : CollatzResearch.WordTrace tailWord_1840948 prefixEnd_1840948 945291183933368516183641 := by
  unfold tailWord_1840948
  simp only [CollatzResearch.WordTrace]
  refine ⟨33572444867283639866069749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44763259823044853154759665 33572444867283639866069749)
  ·
    refine ⟨3147416706307841237444039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33572444867283639866069749 3147416706307841237444039)
    ·
      refine ⟨4721125059461761856166059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3147416706307841237444039 4721125059461761856166059)
      ·
        refine ⟨7081687589192642784249089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4721125059461761856166059 7081687589192642784249089)
        ·
          refine ⟨5311265691894482088186817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7081687589192642784249089 5311265691894482088186817)
          ·
            refine ⟨3983449268920861566140113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5311265691894482088186817 3983449268920861566140113)
            ·
              refine ⟨2987586951690646174605085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3983449268920861566140113 2987586951690646174605085)
              ·
                refine ⟨1120345106883992315476907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2987586951690646174605085 1120345106883992315476907)
                ·
                  refine ⟨1680517660325988473215361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1120345106883992315476907 1680517660325988473215361)
                  ·
                    refine ⟨1260388245244491354911521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1680517660325988473215361 1260388245244491354911521)
                    ·
                      refine ⟨945291183933368516183641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1260388245244491354911521 945291183933368516183641)
                      ·
                        rfl

theorem cell23_1840948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_1840948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1840948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1840948 prefixEnd_1840948 := by exact prefixLift 1840948
  have htrace : WordTrace (prefixWord ++ tailWord_1840948) baseStart_1840948 baseEnd_1840948 := by
    simpa [prefixWord, tailWord_1840948, baseEnd_1840948] using wordTrace_append hprefix tailTrace_1840948
  have hstable : (prefixWord ++ tailWord_1840948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840948).length < 2 ^ (prefixWord ++ tailWord_1840948).sum := by decide
  have hdescent : baseEnd_1840948 < baseStart_1840948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840963 : List Nat := [1, 1, 1, 3, 1, 5, 1, 2, 2, 6]
def baseStart_1840963 : Nat := 118140960795 + 1840963 * 2 ^ 59
def prefixEnd_1840963 : Nat := 4983230072969 + 3 ^ 40 * 1840963 * 2
def baseEnd_1840963 : Nat := 315099628714395319165357

theorem tailTrace_1840963 : CollatzResearch.WordTrace tailWord_1840963 prefixEnd_1840963 315099628714395319165357 := by
  unfold tailWord_1840963
  simp only [CollatzResearch.WordTrace]
  refine ⟨67145436829512937293935543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44763624553008624862623695 67145436829512937293935543)
  ·
    refine ⟨100718155244269405940903315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67145436829512937293935543 100718155244269405940903315)
    ·
      refine ⟨151077232866404108911354973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100718155244269405940903315 151077232866404108911354973)
      ·
        refine ⟨56653962324901540841758115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151077232866404108911354973 56653962324901540841758115)
        ·
          refine ⟨84980943487352311262637173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56653962324901540841758115 84980943487352311262637173)
          ·
            refine ⟨7966963451939279180872235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84980943487352311262637173 7966963451939279180872235)
            ·
              refine ⟨11950445177908918771308353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7966963451939279180872235 11950445177908918771308353)
              ·
                refine ⟨8962833883431689078481265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11950445177908918771308353 8962833883431689078481265)
                ·
                  refine ⟨6722125412573766808860949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8962833883431689078481265 6722125412573766808860949)
                  ·
                    refine ⟨315099628714395319165357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6722125412573766808860949 315099628714395319165357)
                    ·
                      rfl

theorem cell23_1840963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2, 6].length) (baseStart_1840963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1840963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1840963 prefixEnd_1840963 := by exact prefixLift 1840963
  have htrace : WordTrace (prefixWord ++ tailWord_1840963) baseStart_1840963 baseEnd_1840963 := by
    simpa [prefixWord, tailWord_1840963, baseEnd_1840963] using wordTrace_append hprefix tailTrace_1840963
  have hstable : (prefixWord ++ tailWord_1840963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840963).length < 2 ^ (prefixWord ++ tailWord_1840963).sum := by decide
  have hdescent : baseEnd_1840963 < baseStart_1840963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840980 : List Nat := [2, 4, 1, 1, 3, 1, 2, 1, 2, 6]
def baseStart_1840980 : Nat := 118140960795 + 1840980 * 2 ^ 59
def prefixEnd_1840980 : Nat := 4983230072969 + 3 ^ 40 * 1840980 * 2
def baseEnd_1840980 : Nat := 315102538438104130327831

theorem tailTrace_1840980 : CollatzResearch.WordTrace tailWord_1840980 prefixEnd_1840980 315102538438104130327831 := by
  unfold tailWord_1840980
  simp only [CollatzResearch.WordTrace]
  refine ⟨33573028435225674598652197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44764037913634232798202929 33573028435225674598652197)
  ·
    refine ⟨6294942831604813987247287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33573028435225674598652197 6294942831604813987247287)
    ·
      refine ⟨9442414247407220980870931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6294942831604813987247287 9442414247407220980870931)
      ·
        refine ⟨14163621371110831471306397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9442414247407220980870931 14163621371110831471306397)
        ·
          refine ⟨5311358014166561801739899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14163621371110831471306397 5311358014166561801739899)
          ·
            refine ⟨7967037021249842702609849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5311358014166561801739899 7967037021249842702609849)
            ·
              refine ⟨5975277765937382026957387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7967037021249842702609849 5975277765937382026957387)
              ·
                refine ⟨8962916648906073040436081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5975277765937382026957387 8962916648906073040436081)
                ·
                  refine ⟨6722187486679554780327061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8962916648906073040436081 6722187486679554780327061)
                  ·
                    refine ⟨315102538438104130327831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6722187486679554780327061 315102538438104130327831)
                    ·
                      rfl

theorem cell23_1840980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_1840980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1840980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1840980 prefixEnd_1840980 := by exact prefixLift 1840980
  have htrace : WordTrace (prefixWord ++ tailWord_1840980) baseStart_1840980 baseEnd_1840980 := by
    simpa [prefixWord, tailWord_1840980, baseEnd_1840980] using wordTrace_append hprefix tailTrace_1840980
  have hstable : (prefixWord ++ tailWord_1840980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840980).length < 2 ^ (prefixWord ++ tailWord_1840980).sum := by decide
  have hdescent : baseEnd_1840980 < baseStart_1840980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840993 : List Nat := [1, 2, 3, 1, 1, 1, 3, 4, 7]
def baseStart_1840993 : Nat := 118140960795 + 1840993 * 2 ^ 59
def prefixEnd_1840993 : Nat := 4983230072969 + 3 ^ 40 * 1840993 * 2
def baseEnd_1840993 : Nat := 105034921173646760013437

theorem tailTrace_1840993 : CollatzResearch.WordTrace tailWord_1840993 prefixEnd_1840993 105034921173646760013437 := by
  unfold tailWord_1840993
  simp only [CollatzResearch.WordTrace]
  refine ⟨67146531019404252417527633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44764354012936168278351755 67146531019404252417527633)
  ·
    refine ⟨50359898264553189313145725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67146531019404252417527633 50359898264553189313145725)
    ·
      refine ⟨18884961849207445992429647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50359898264553189313145725 18884961849207445992429647)
      ·
        refine ⟨28327442773811168988644471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18884961849207445992429647 28327442773811168988644471)
        ·
          refine ⟨42491164160716753482966707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28327442773811168988644471 42491164160716753482966707)
          ·
            refine ⟨63736746241075130224450061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42491164160716753482966707 63736746241075130224450061)
            ·
              refine ⟨23901279840403173834168773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63736746241075130224450061 23901279840403173834168773)
              ·
                refine ⟨4481489970075595093906645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23901279840403173834168773 4481489970075595093906645)
                ·
                  refine ⟨105034921173646760013437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4481489970075595093906645 105034921173646760013437)
                  ·
                    rfl

theorem cell23_1840993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4, 7].length) (baseStart_1840993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1840993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1840993 prefixEnd_1840993 := by exact prefixLift 1840993
  have htrace : WordTrace (prefixWord ++ tailWord_1840993) baseStart_1840993 baseEnd_1840993 := by
    simpa [prefixWord, tailWord_1840993, baseEnd_1840993] using wordTrace_append hprefix tailTrace_1840993
  have hstable : (prefixWord ++ tailWord_1840993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840993).length < 2 ^ (prefixWord ++ tailWord_1840993).sum := by decide
  have hdescent : baseEnd_1840993 < baseStart_1840993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841038 : List Nat := [4, 1, 1, 5, 1, 1, 1, 3, 2, 2, 2]
def baseStart_1841038 : Nat := 118140960795 + 1841038 * 2 ^ 59
def prefixEnd_1841038 : Nat := 4983230072969 + 3 ^ 40 * 1841038 * 2
def baseEnd_1841038 : Nat := 945337397192273164058227

theorem tailTrace_1841038 : CollatzResearch.WordTrace tailWord_1841038 prefixEnd_1841038 945337397192273164058227 := by
  unfold tailWord_1841038
  simp only [CollatzResearch.WordTrace]
  refine ⟨8393521538030153137864471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44765448202827483401943845 8393521538030153137864471)
  ·
    refine ⟨12590282307045229706796707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8393521538030153137864471 12590282307045229706796707)
    ·
      refine ⟨18885423460567844560195061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12590282307045229706796707 18885423460567844560195061)
      ·
        refine ⟨1770508449428235427518287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18885423460567844560195061 1770508449428235427518287)
        ·
          refine ⟨2655762674142353141277431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1770508449428235427518287 2655762674142353141277431)
          ·
            refine ⟨3983644011213529711916147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2655762674142353141277431 3983644011213529711916147)
            ·
              refine ⟨5975466016820294567874221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3983644011213529711916147 5975466016820294567874221)
              ·
                refine ⟨2240799756307610462952833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5975466016820294567874221 2240799756307610462952833)
                ·
                  refine ⟨1680599817230707847214625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2240799756307610462952833 1680599817230707847214625)
                  ·
                    refine ⟨1260449862923030885410969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1680599817230707847214625 1260449862923030885410969)
                    ·
                      refine ⟨945337397192273164058227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1260449862923030885410969 945337397192273164058227)
                      ·
                        rfl

theorem cell23_1841038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_1841038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1841038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1841038 prefixEnd_1841038 := by exact prefixLift 1841038
  have htrace : WordTrace (prefixWord ++ tailWord_1841038) baseStart_1841038 baseEnd_1841038 := by
    simpa [prefixWord, tailWord_1841038, baseEnd_1841038] using wordTrace_append hprefix tailTrace_1841038
  have hstable : (prefixWord ++ tailWord_1841038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841038).length < 2 ^ (prefixWord ++ tailWord_1841038).sum := by decide
  have hdescent : baseEnd_1841038 < baseStart_1841038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841077 : List Nat := [1, 3, 3, 2, 1, 2, 2, 2, 2, 1, 4]
def baseStart_1841077 : Nat := 118140960795 + 1841077 * 2 ^ 59
def prefixEnd_1841077 : Nat := 4983230072969 + 3 ^ 40 * 1841077 * 2
def baseEnd_1841077 : Nat := 945357422937798511470547

theorem tailTrace_1841077 : CollatzResearch.WordTrace tailWord_1841077 prefixEnd_1841077 945357422937798511470547 := by
  unfold tailWord_1841077
  simp only [CollatzResearch.WordTrace]
  refine ⟨67149594751099934763585485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44766396500733289842390323 67149594751099934763585485)
  ·
    refine ⟨25181098031662475536344557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67149594751099934763585485 25181098031662475536344557)
    ·
      refine ⟨9442911761873428326129209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25181098031662475536344557 9442911761873428326129209)
      ·
        refine ⟨7082183821405071244596907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9442911761873428326129209 7082183821405071244596907)
        ·
          refine ⟨10623275732107606866895361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7082183821405071244596907 10623275732107606866895361)
          ·
            refine ⟨7967456799080705150171521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10623275732107606866895361 7967456799080705150171521)
            ·
              refine ⟨5975592599310528862628641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7967456799080705150171521 5975592599310528862628641)
              ·
                refine ⟨4481694449482896646971481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5975592599310528862628641 4481694449482896646971481)
                ·
                  refine ⟨3361270837112172485228611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4481694449482896646971481 3361270837112172485228611)
                  ·
                    refine ⟨5041906255668258727842917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3361270837112172485228611 5041906255668258727842917)
                    ·
                      refine ⟨945357422937798511470547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5041906255668258727842917 945357422937798511470547)
                      ·
                        rfl

theorem cell23_1841077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_1841077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1841077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1841077 prefixEnd_1841077 := by exact prefixLift 1841077
  have htrace : WordTrace (prefixWord ++ tailWord_1841077) baseStart_1841077 baseEnd_1841077 := by
    simpa [prefixWord, tailWord_1841077, baseEnd_1841077] using wordTrace_append hprefix tailTrace_1841077
  have hstable : (prefixWord ++ tailWord_1841077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841077).length < 2 ^ (prefixWord ++ tailWord_1841077).sum := by decide
  have hdescent : baseEnd_1841077 < baseStart_1841077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841134 : List Nat := [4, 1, 2, 1, 3, 3, 1, 2, 6]
def baseStart_1841134 : Nat := 118140960795 + 1841134 * 2 ^ 59
def prefixEnd_1841134 : Nat := 4983230072969 + 3 ^ 40 * 1841134 * 2
def baseEnd_1841134 : Nat := 105042965703900532050865

theorem tailTrace_1841134 : CollatzResearch.WordTrace tailWord_1841134 prefixEnd_1841134 105042965703900532050865 := by
  unfold tailWord_1841134
  simp only [CollatzResearch.WordTrace]
  refine ⟨8393959213986679187301307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44767782474595622332273637 8393959213986679187301307)
  ·
    refine ⟨12590938820980018780951961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8393959213986679187301307 12590938820980018780951961)
    ·
      refine ⟨9443204115735014085713971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12590938820980018780951961 9443204115735014085713971)
      ·
        refine ⟨14164806173602521128570957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9443204115735014085713971 14164806173602521128570957)
        ·
          refine ⟨5311802315100945423214109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14164806173602521128570957 5311802315100945423214109)
          ·
            refine ⟨1991925868162854533705291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5311802315100945423214109 1991925868162854533705291)
            ·
              refine ⟨2987888802244281800557937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1991925868162854533705291 2987888802244281800557937)
              ·
                refine ⟨2240916601683211350418453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2987888802244281800557937 2240916601683211350418453)
                ·
                  refine ⟨105042965703900532050865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2240916601683211350418453 105042965703900532050865)
                  ·
                    rfl

theorem cell23_1841134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 2, 6].length) (baseStart_1841134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1841134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1841134 prefixEnd_1841134 := by exact prefixLift 1841134
  have htrace : WordTrace (prefixWord ++ tailWord_1841134) baseStart_1841134 baseEnd_1841134 := by
    simpa [prefixWord, tailWord_1841134, baseEnd_1841134] using wordTrace_append hprefix tailTrace_1841134
  have hstable : (prefixWord ++ tailWord_1841134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841134).length < 2 ^ (prefixWord ++ tailWord_1841134).sum := by decide
  have hdescent : baseEnd_1841134 < baseStart_1841134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841172 : List Nat := [2, 4, 3, 2, 2, 1, 1, 3, 1, 4]
def baseStart_1841172 : Nat := 118140960795 + 1841172 * 2 ^ 59
def prefixEnd_1841172 : Nat := 4983230072969 + 3 ^ 40 * 1841172 * 2
def baseEnd_1841172 : Nat := 315135401199991879927537

theorem tailTrace_1841172 : CollatzResearch.WordTrace tailWord_1841172 prefixEnd_1841172 315135401199991879927537 := by
  unfold tailWord_1841172
  simp only [CollatzResearch.WordTrace]
  refine ⟨33576529842877882994146885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44768706457170510658862513 33576529842877882994146885)
  ·
    refine ⟨6295599345539603061402541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33576529842877882994146885 6295599345539603061402541)
    ·
      refine ⟨2360849754577351148025953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6295599345539603061402541 2360849754577351148025953)
      ·
        refine ⟨1770637315933013361019465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2360849754577351148025953 1770637315933013361019465)
        ·
          refine ⟨1327977986949760020764599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1770637315933013361019465 1327977986949760020764599)
          ·
            refine ⟨1991966980424640031146899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1327977986949760020764599 1991966980424640031146899)
            ·
              refine ⟨2987950470636960046720349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1991966980424640031146899 2987950470636960046720349)
              ·
                refine ⟨1120481426488860017520131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2987950470636960046720349 1120481426488860017520131)
                ·
                  refine ⟨1680722139733290026280197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1120481426488860017520131 1680722139733290026280197)
                  ·
                    refine ⟨315135401199991879927537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1680722139733290026280197 315135401199991879927537)
                    ·
                      rfl

theorem cell23_1841172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_1841172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1841172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1841172 prefixEnd_1841172 := by exact prefixLift 1841172
  have htrace : WordTrace (prefixWord ++ tailWord_1841172) baseStart_1841172 baseEnd_1841172 := by
    simpa [prefixWord, tailWord_1841172, baseEnd_1841172] using wordTrace_append hprefix tailTrace_1841172
  have hstable : (prefixWord ++ tailWord_1841172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841172).length < 2 ^ (prefixWord ++ tailWord_1841172).sum := by decide
  have hdescent : baseEnd_1841172 < baseStart_1841172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841178 : List Nat := [3, 1, 1, 3, 1, 5, 1, 3, 1, 1, 3]
def baseStart_1841178 : Nat := 118140960795 + 1841178 * 2 ^ 59
def prefixEnd_1841178 : Nat := 4983230072969 + 3 ^ 40 * 1841178 * 2
def baseEnd_1841178 : Nat := 945409284483902616307583

theorem tailTrace_1841178 : CollatzResearch.WordTrace tailWord_1841178 prefixEnd_1841178 945409284483902616307583 := by
  unfold tailWord_1841178
  simp only [CollatzResearch.WordTrace]
  refine ⟨16788319630933507253253047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44768852349156019342008125 16788319630933507253253047)
  ·
    refine ⟨25182479446400260879879571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16788319630933507253253047 25182479446400260879879571)
    ·
      refine ⟨37773719169600391319819357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25182479446400260879879571 37773719169600391319819357)
      ·
        refine ⟨14165144688600146744932259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37773719169600391319819357 14165144688600146744932259)
        ·
          refine ⟨21247717032900220117398389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14165144688600146744932259 21247717032900220117398389)
          ·
            refine ⟨1991973471834395636006099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21247717032900220117398389 1991973471834395636006099)
            ·
              refine ⟨2987960207751593454009149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1991973471834395636006099 2987960207751593454009149)
              ·
                refine ⟨1120485077906847545253431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2987960207751593454009149 1120485077906847545253431)
                ·
                  refine ⟨1680727616860271317880147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1120485077906847545253431 1680727616860271317880147)
                  ·
                    refine ⟨2521091425290406976820221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1680727616860271317880147 2521091425290406976820221)
                    ·
                      refine ⟨945409284483902616307583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2521091425290406976820221 945409284483902616307583)
                      ·
                        rfl

theorem cell23_1841178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 3, 1, 1, 3].length) (baseStart_1841178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1841178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1841178 prefixEnd_1841178 := by exact prefixLift 1841178
  have htrace : WordTrace (prefixWord ++ tailWord_1841178) baseStart_1841178 baseEnd_1841178 := by
    simpa [prefixWord, tailWord_1841178, baseEnd_1841178] using wordTrace_append hprefix tailTrace_1841178
  have hstable : (prefixWord ++ tailWord_1841178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841178).length < 2 ^ (prefixWord ++ tailWord_1841178).sum := by decide
  have hdescent : baseEnd_1841178 < baseStart_1841178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841187 : List Nat := [1, 1, 1, 4, 3, 1, 4, 1, 1, 1, 5]
def baseStart_1841187 : Nat := 118140960795 + 1841187 * 2 ^ 59
def prefixEnd_1841187 : Nat := 4983230072969 + 3 ^ 40 * 1841187 * 2
def baseEnd_1841187 : Nat := 945413905809793081095041

theorem tailTrace_1841187 : CollatzResearch.WordTrace tailWord_1841187 prefixEnd_1841187 945413905809793081095041 := by
  unfold tailWord_1841187
  simp only [CollatzResearch.WordTrace]
  refine ⟨67153606780701423550089815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44769071187134282366726543 67153606780701423550089815)
  ·
    refine ⟨100730410171052135325134723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67153606780701423550089815 100730410171052135325134723)
    ·
      refine ⟨151095615256578202987702085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100730410171052135325134723 151095615256578202987702085)
      ·
        refine ⟨28330427860608413060194141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151095615256578202987702085 28330427860608413060194141)
        ·
          refine ⟨10623910447728154897572803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28330427860608413060194141 10623910447728154897572803)
          ·
            refine ⟨15935865671592232346359205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10623910447728154897572803 15935865671592232346359205)
            ·
              refine ⟨2987974813423543564942351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15935865671592232346359205 2987974813423543564942351)
              ·
                refine ⟨4481962220135315347413527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2987974813423543564942351 4481962220135315347413527)
                ·
                  refine ⟨6722943330202973021120291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4481962220135315347413527 6722943330202973021120291)
                  ·
                    refine ⟨10084414995304459531680437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6722943330202973021120291 10084414995304459531680437)
                    ·
                      refine ⟨945413905809793081095041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10084414995304459531680437 945413905809793081095041)
                      ·
                        rfl

theorem cell23_1841187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 1, 1, 1, 5].length) (baseStart_1841187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1841187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1841187 prefixEnd_1841187 := by exact prefixLift 1841187
  have htrace : WordTrace (prefixWord ++ tailWord_1841187) baseStart_1841187 baseEnd_1841187 := by
    simpa [prefixWord, tailWord_1841187, baseEnd_1841187] using wordTrace_append hprefix tailTrace_1841187
  have hstable : (prefixWord ++ tailWord_1841187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841187).length < 2 ^ (prefixWord ++ tailWord_1841187).sum := by decide
  have hdescent : baseEnd_1841187 < baseStart_1841187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841194 : List Nat := [3, 1, 4, 1, 2, 1, 2, 1, 4, 4]
def baseStart_1841194 : Nat := 118140960795 + 1841194 * 2 ^ 59
def prefixEnd_1841194 : Nat := 4983230072969 + 3 ^ 40 * 1841194 * 2
def baseEnd_1841194 : Nat := 315139166724791517902503

theorem tailTrace_1841194 : CollatzResearch.WordTrace tailWord_1841194 prefixEnd_1841194 315139166724791517902503 := by
  unfold tailWord_1841194
  simp only [CollatzResearch.WordTrace]
  refine ⟨16788465522919015936398659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44769241394450709163729757 16788465522919015936398659)
  ·
    refine ⟨25182698284378523904597989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16788465522919015936398659 25182698284378523904597989)
    ·
      refine ⟨4721755928320973232112123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25182698284378523904597989 4721755928320973232112123)
      ·
        refine ⟨7082633892481459848168185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4721755928320973232112123 7082633892481459848168185)
        ·
          refine ⟨5311975419361094886126139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7082633892481459848168185 5311975419361094886126139)
          ·
            refine ⟨7967963129041642329189209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5311975419361094886126139 7967963129041642329189209)
            ·
              refine ⟨5975972346781231746891907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7967963129041642329189209 5975972346781231746891907)
              ·
                refine ⟨8963958520171847620337861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5975972346781231746891907 8963958520171847620337861)
                ·
                  refine ⟨1680742222532221428813349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8963958520171847620337861 1680742222532221428813349)
                  ·
                    refine ⟨315139166724791517902503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1680742222532221428813349 315139166724791517902503)
                    ·
                      rfl

theorem cell23_1841194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_1841194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1841194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1841194 prefixEnd_1841194 := by exact prefixLift 1841194
  have htrace : WordTrace (prefixWord ++ tailWord_1841194) baseStart_1841194 baseEnd_1841194 := by
    simpa [prefixWord, tailWord_1841194, baseEnd_1841194] using wordTrace_append hprefix tailTrace_1841194
  have hstable : (prefixWord ++ tailWord_1841194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841194).length < 2 ^ (prefixWord ++ tailWord_1841194).sum := by decide
  have hdescent : baseEnd_1841194 < baseStart_1841194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841201 : List Nat := [1, 2, 2, 3, 1, 3, 3, 1, 3, 2, 2]
def baseStart_1841201 : Nat := 118140960795 + 1841201 * 2 ^ 59
def prefixEnd_1841201 : Nat := 4983230072969 + 3 ^ 40 * 1841201 * 2
def baseEnd_1841201 : Nat := 945421094538956026319977

theorem tailTrace_1841201 : CollatzResearch.WordTrace tailWord_1841201 prefixEnd_1841201 945421094538956026319977 := by
  unfold tailWord_1841201
  simp only [CollatzResearch.WordTrace]
  refine ⟨67154117402650703941099457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44769411601767135960732971 67154117402650703941099457)
  ·
    refine ⟨50365588051988027955824593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67154117402650703941099457 50365588051988027955824593)
    ·
      refine ⟨37774191038991020966868445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50365588051988027955824593 37774191038991020966868445)
      ·
        refine ⟨14165321639621632862575667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37774191038991020966868445 14165321639621632862575667)
        ·
          refine ⟨21247982459432449293863501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14165321639621632862575667 21247982459432449293863501)
          ·
            refine ⟨7967993422287168485198813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21247982459432449293863501 7967993422287168485198813)
            ·
              refine ⟨2987997533357688181949555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7967993422287168485198813 2987997533357688181949555)
              ·
                refine ⟨4481996300036532272924333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2987997533357688181949555 4481996300036532272924333)
                ·
                  refine ⟨1680748612513699602346625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4481996300036532272924333 1680748612513699602346625)
                  ·
                    refine ⟨1260561459385274701759969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1680748612513699602346625 1260561459385274701759969)
                    ·
                      refine ⟨945421094538956026319977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1260561459385274701759969 945421094538956026319977)
                      ·
                        rfl

theorem cell23_1841201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 1, 3, 2, 2].length) (baseStart_1841201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1841201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1841201 prefixEnd_1841201 := by exact prefixLift 1841201
  have htrace : WordTrace (prefixWord ++ tailWord_1841201) baseStart_1841201 baseEnd_1841201 := by
    simpa [prefixWord, tailWord_1841201, baseEnd_1841201] using wordTrace_append hprefix tailTrace_1841201
  have hstable : (prefixWord ++ tailWord_1841201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841201).length < 2 ^ (prefixWord ++ tailWord_1841201).sum := by decide
  have hdescent : baseEnd_1841201 < baseStart_1841201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841210 : List Nat := [3, 1, 1, 1, 3, 1, 1, 1, 1, 4, 6]
def baseStart_1841210 : Nat := 118140960795 + 1841210 * 2 ^ 59
def prefixEnd_1841210 : Nat := 4983230072969 + 3 ^ 40 * 1841210 * 2
def baseEnd_1841210 : Nat := 945425715864846491107435

theorem tailTrace_1841210 : CollatzResearch.WordTrace tailWord_1841210 prefixEnd_1841210 945425715864846491107435 := by
  unfold tailWord_1841210
  simp only [CollatzResearch.WordTrace]
  refine ⟨16788611414904524619544271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44769630439745398985451389 16788611414904524619544271)
  ·
    refine ⟨25182917122356786929316407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16788611414904524619544271 25182917122356786929316407)
    ·
      refine ⟨37774375683535180393974611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25182917122356786929316407 37774375683535180393974611)
      ·
        refine ⟨56661563525302770590961917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37774375683535180393974611 56661563525302770590961917)
        ·
          refine ⟨21248086321988538971610719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56661563525302770590961917 21248086321988538971610719)
          ·
            refine ⟨31872129482982808457416079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21248086321988538971610719 31872129482982808457416079)
            ·
              refine ⟨47808194224474212686124119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31872129482982808457416079 47808194224474212686124119)
              ·
                refine ⟨71712291336711319029186179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47808194224474212686124119 71712291336711319029186179)
                ·
                  refine ⟨107568437005066978543779269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71712291336711319029186179 107568437005066978543779269)
                  ·
                    refine ⟨20169081938450058476958613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 107568437005066978543779269 20169081938450058476958613)
                    ·
                      refine ⟨945425715864846491107435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20169081938450058476958613 945425715864846491107435)
                      ·
                        rfl

theorem cell23_1841210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 1, 4, 6].length) (baseStart_1841210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1841210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1841210 prefixEnd_1841210 := by exact prefixLift 1841210
  have htrace : WordTrace (prefixWord ++ tailWord_1841210) baseStart_1841210 baseEnd_1841210 := by
    simpa [prefixWord, tailWord_1841210, baseEnd_1841210] using wordTrace_append hprefix tailTrace_1841210
  have hstable : (prefixWord ++ tailWord_1841210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841210).length < 2 ^ (prefixWord ++ tailWord_1841210).sum := by decide
  have hdescent : baseEnd_1841210 < baseStart_1841210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841227 : List Nat := [1, 1, 1, 1, 3, 1, 2, 2, 2, 7, 2]
def baseStart_1841227 : Nat := 118140960795 + 1841227 * 2 ^ 59
def prefixEnd_1841227 : Nat := 4983230072969 + 3 ^ 40 * 1841227 * 2
def baseEnd_1841227 : Nat := 945434445035972924594857

theorem tailTrace_1841227 : CollatzResearch.WordTrace tailWord_1841227 prefixEnd_1841227 945434445035972924594857 := by
  unfold tailWord_1841227
  simp only [CollatzResearch.WordTrace]
  refine ⟨67155065700556510381545935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44770043800371006921030623 67155065700556510381545935)
  ·
    refine ⟨100732598550834765572318903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67155065700556510381545935 100732598550834765572318903)
    ·
      refine ⟨151098897826252148358478355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100732598550834765572318903 151098897826252148358478355)
      ·
        refine ⟨226648346739378222537717533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151098897826252148358478355 226648346739378222537717533)
        ·
          refine ⟨84993130027266833451644075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226648346739378222537717533 84993130027266833451644075)
          ·
            refine ⟨127489695040900250177466113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84993130027266833451644075 127489695040900250177466113)
            ·
              refine ⟨95617271280675187633099585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127489695040900250177466113 95617271280675187633099585)
              ·
                refine ⟨71712953460506390724824689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95617271280675187633099585 71712953460506390724824689)
                ·
                  refine ⟨53784715095379793043618517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71712953460506390724824689 53784715095379793043618517)
                  ·
                    refine ⟨1260579260047963899459809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53784715095379793043618517 1260579260047963899459809)
                    ·
                      refine ⟨945434445035972924594857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1260579260047963899459809 945434445035972924594857)
                      ·
                        rfl

theorem cell23_1841227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 7, 2].length) (baseStart_1841227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1841227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1841227 prefixEnd_1841227 := by exact prefixLift 1841227
  have htrace : WordTrace (prefixWord ++ tailWord_1841227) baseStart_1841227 baseEnd_1841227 := by
    simpa [prefixWord, tailWord_1841227, baseEnd_1841227] using wordTrace_append hprefix tailTrace_1841227
  have hstable : (prefixWord ++ tailWord_1841227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841227).length < 2 ^ (prefixWord ++ tailWord_1841227).sum := by decide
  have hdescent : baseEnd_1841227 < baseStart_1841227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841238 : List Nat := [5, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5]
def baseStart_1841238 : Nat := 118140960795 + 1841238 * 2 ^ 59
def prefixEnd_1841238 : Nat := 4983230072969 + 3 ^ 40 * 1841238 * 2
def baseEnd_1841238 : Nat := 945440093323172381557307

theorem tailTrace_1841238 : CollatzResearch.WordTrace tailWord_1841238 prefixEnd_1841238 945440093323172381557307 := by
  unfold tailWord_1841238
  simp only [CollatzResearch.WordTrace]
  refine ⟨4197216681469791203762273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44770311269011106173464245 4197216681469791203762273)
  ·
    refine ⟨3147912511102343402821705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4197216681469791203762273 3147912511102343402821705)
    ·
      refine ⟨2360934383326757552116279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3147912511102343402821705 2360934383326757552116279)
      ·
        refine ⟨3541401574990136328174419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2360934383326757552116279 3541401574990136328174419)
        ·
          refine ⟨5312102362485204492261629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3541401574990136328174419 5312102362485204492261629)
          ·
            refine ⟨1992038385931951684598111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5312102362485204492261629 1992038385931951684598111)
            ·
              refine ⟨2988057578897927526897167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1992038385931951684598111 2988057578897927526897167)
              ·
                refine ⟨4482086368346891290345751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2988057578897927526897167 4482086368346891290345751)
                ·
                  refine ⟨6723129552520336935518627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4482086368346891290345751 6723129552520336935518627)
                  ·
                    refine ⟨10084694328780505403277941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6723129552520336935518627 10084694328780505403277941)
                    ·
                      refine ⟨945440093323172381557307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10084694328780505403277941 945440093323172381557307)
                      ·
                        rfl

theorem cell23_1841238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_1841238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1841238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1841238 prefixEnd_1841238 := by exact prefixLift 1841238
  have htrace : WordTrace (prefixWord ++ tailWord_1841238) baseStart_1841238 baseEnd_1841238 := by
    simpa [prefixWord, tailWord_1841238, baseEnd_1841238] using wordTrace_append hprefix tailTrace_1841238
  have hstable : (prefixWord ++ tailWord_1841238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841238).length < 2 ^ (prefixWord ++ tailWord_1841238).sum := by decide
  have hdescent : baseEnd_1841238 < baseStart_1841238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841246 : List Nat := [4, 4, 1, 1, 3, 1, 2, 2, 1, 1, 3]
def baseStart_1841246 : Nat := 118140960795 + 1841246 * 2 ^ 59
def prefixEnd_1841246 : Nat := 4983230072969 + 3 ^ 40 * 1841246 * 2
def baseEnd_1841246 : Nat := 945444201168408350257271

theorem tailTrace_1841246 : CollatzResearch.WordTrace tailWord_1841246 prefixEnd_1841246 945444201168408350257271 := by
  unfold tailWord_1841246
  simp only [CollatzResearch.WordTrace]
  refine ⟨8394469835935959578310949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44770505791658451084325061 8394469835935959578310949)
  ·
    refine ⟨1573963094237992420933303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8394469835935959578310949 1573963094237992420933303)
    ·
      refine ⟨2360944641356988631399955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1573963094237992420933303 2360944641356988631399955)
      ·
        refine ⟨3541416962035482947099933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2360944641356988631399955 3541416962035482947099933)
        ·
          refine ⟨1328031360763306105162475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3541416962035482947099933 1328031360763306105162475)
          ·
            refine ⟨1992047041144959157743713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1328031360763306105162475 1992047041144959157743713)
            ·
              refine ⟨1494035280858719368307785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1992047041144959157743713 1494035280858719368307785)
              ·
                refine ⟨1120526460644039526230839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1494035280858719368307785 1120526460644039526230839)
                ·
                  refine ⟨1680789690966059289346259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1120526460644039526230839 1680789690966059289346259)
                  ·
                    refine ⟨2521184536449088934019389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1680789690966059289346259 2521184536449088934019389)
                    ·
                      refine ⟨945444201168408350257271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2521184536449088934019389 945444201168408350257271)
                      ·
                        rfl

theorem cell23_1841246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_1841246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1841246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1841246 prefixEnd_1841246 := by exact prefixLift 1841246
  have htrace : WordTrace (prefixWord ++ tailWord_1841246) baseStart_1841246 baseEnd_1841246 := by
    simpa [prefixWord, tailWord_1841246, baseEnd_1841246] using wordTrace_append hprefix tailTrace_1841246
  have hstable : (prefixWord ++ tailWord_1841246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841246).length < 2 ^ (prefixWord ++ tailWord_1841246).sum := by decide
  have hdescent : baseEnd_1841246 < baseStart_1841246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841307 : List Nat := [1, 1, 1, 1, 1, 1, 2, 5, 4, 3, 3]
def baseStart_1841307 : Nat := 118140960795 + 1841307 * 2 ^ 59
def prefixEnd_1841307 : Nat := 4983230072969 + 3 ^ 40 * 1841307 * 2
def baseEnd_1841307 : Nat := 945475523488332611594489

theorem tailTrace_1841307 : CollatzResearch.WordTrace tailWord_1841307 prefixEnd_1841307 945475523488332611594489 := by
  unfold tailWord_1841307
  simp only [CollatzResearch.WordTrace]
  refine ⟨67157983540266684044458175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44771989026844456029638783 67157983540266684044458175)
  ·
    refine ⟨100736975310400026066687263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67157983540266684044458175 100736975310400026066687263)
    ·
      refine ⟨151105462965600039100030895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100736975310400026066687263 151105462965600039100030895)
      ·
        refine ⟨226658194448400058650046343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151105462965600039100030895 226658194448400058650046343)
        ·
          refine ⟨339987291672600087975069515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226658194448400058650046343 339987291672600087975069515)
          ·
            refine ⟨509980937508900131962604273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339987291672600087975069515 509980937508900131962604273)
            ·
              refine ⟨382485703131675098971953205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 509980937508900131962604273 382485703131675098971953205)
              ·
                refine ⟨35858034668594540528620613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 382485703131675098971953205 35858034668594540528620613)
                ·
                  refine ⟨6723381500361476349116365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35858034668594540528620613 6723381500361476349116365)
                  ·
                    refine ⟨2521268062635553630918637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6723381500361476349116365 2521268062635553630918637)
                    ·
                      refine ⟨945475523488332611594489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2521268062635553630918637 945475523488332611594489)
                      ·
                        rfl

theorem cell23_1841307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4, 3, 3].length) (baseStart_1841307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1841307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1841307 prefixEnd_1841307 := by exact prefixLift 1841307
  have htrace : WordTrace (prefixWord ++ tailWord_1841307) baseStart_1841307 baseEnd_1841307 := by
    simpa [prefixWord, tailWord_1841307, baseEnd_1841307] using wordTrace_append hprefix tailTrace_1841307
  have hstable : (prefixWord ++ tailWord_1841307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841307).length < 2 ^ (prefixWord ++ tailWord_1841307).sum := by decide
  have hdescent : baseEnd_1841307 < baseStart_1841307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841314 : List Nat := [3, 3, 1, 3, 1, 1, 1, 3, 7]
def baseStart_1841314 : Nat := 118140960795 + 1841314 * 2 ^ 59
def prefixEnd_1841314 : Nat := 4983230072969 + 3 ^ 40 * 1841314 * 2
def baseEnd_1841314 : Nat := 105053235316990453800773

theorem tailTrace_1841314 : CollatzResearch.WordTrace tailWord_1841314 prefixEnd_1841314 105053235316990453800773 := by
  unfold tailWord_1841314
  simp only [CollatzResearch.WordTrace]
  refine ⟨16789559712810331059990749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44772159234160882826641997 16789559712810331059990749)
  ·
    refine ⟨6296084892303874147496531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16789559712810331059990749 6296084892303874147496531)
    ·
      refine ⟨9444127338455811221244797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6296084892303874147496531 9444127338455811221244797)
      ·
        refine ⟨3541547751920929207966799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9444127338455811221244797 3541547751920929207966799)
        ·
          refine ⟨5312321627881393811950199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3541547751920929207966799 5312321627881393811950199)
          ·
            refine ⟨7968482441822090717925299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5312321627881393811950199 7968482441822090717925299)
            ·
              refine ⟨11952723662733136076887949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7968482441822090717925299 11952723662733136076887949)
              ·
                refine ⟨4482271373524926028832981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11952723662733136076887949 4482271373524926028832981)
                ·
                  refine ⟨105053235316990453800773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4482271373524926028832981 105053235316990453800773)
                  ·
                    rfl

theorem cell23_1841314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 3, 7].length) (baseStart_1841314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1841314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1841314 prefixEnd_1841314 := by exact prefixLift 1841314
  have htrace : WordTrace (prefixWord ++ tailWord_1841314) baseStart_1841314 baseEnd_1841314 := by
    simpa [prefixWord, tailWord_1841314, baseEnd_1841314] using wordTrace_append hprefix tailTrace_1841314
  have hstable : (prefixWord ++ tailWord_1841314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841314).length < 2 ^ (prefixWord ++ tailWord_1841314).sum := by decide
  have hdescent : baseEnd_1841314 < baseStart_1841314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841348 : List Nat := [2, 3, 3, 1, 2, 3, 1, 3, 5]
def baseStart_1841348 : Nat := 118140960795 + 1841348 * 2 ^ 59
def prefixEnd_1841348 : Nat := 4983230072969 + 3 ^ 40 * 1841348 * 2
def baseEnd_1841348 : Nat := 105055175132796327909089

theorem tailTrace_1841348 : CollatzResearch.WordTrace tailWord_1841348 prefixEnd_1841348 105055175132796327909089 := by
  unfold tailWord_1841348
  simp only [CollatzResearch.WordTrace]
  refine ⟨33579739466559074023350349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44772985955412098697800465 33579739466559074023350349)
  ·
    refine ⟨12592402299959652758756381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33579739466559074023350349 12592402299959652758756381)
    ·
      refine ⟨4722150862484869784533643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12592402299959652758756381 4722150862484869784533643)
      ·
        refine ⟨7083226293727304676800465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4722150862484869784533643 7083226293727304676800465)
        ·
          refine ⟨5312419720295478507600349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7083226293727304676800465 5312419720295478507600349)
          ·
            refine ⟨1992157395110804440350131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5312419720295478507600349 1992157395110804440350131)
            ·
              refine ⟨2988236092666206660525197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1992157395110804440350131 2988236092666206660525197)
              ·
                refine ⟨1120588534749827497696949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2988236092666206660525197 1120588534749827497696949)
                ·
                  refine ⟨105055175132796327909089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1120588534749827497696949 105055175132796327909089)
                  ·
                    rfl

theorem cell23_1841348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 3, 5].length) (baseStart_1841348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1841348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1841348 prefixEnd_1841348 := by exact prefixLift 1841348
  have htrace : WordTrace (prefixWord ++ tailWord_1841348) baseStart_1841348 baseEnd_1841348 := by
    simpa [prefixWord, tailWord_1841348, baseEnd_1841348] using wordTrace_append hprefix tailTrace_1841348
  have hstable : (prefixWord ++ tailWord_1841348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841348).length < 2 ^ (prefixWord ++ tailWord_1841348).sum := by decide
  have hdescent : baseEnd_1841348 < baseStart_1841348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841425 : List Nat := [1, 2, 2, 1, 1, 7, 2, 2, 1, 4]
def baseStart_1841425 : Nat := 118140960795 + 1841425 * 2 ^ 59
def prefixEnd_1841425 : Nat := 4983230072969 + 3 ^ 40 * 1841425 * 2
def baseEnd_1841425 : Nat := 315178704735187716639649

theorem tailTrace_1841425 : CollatzResearch.WordTrace tailWord_1841425 prefixEnd_1841425 315178704735187716639649 := by
  unfold tailWord_1841425
  simp only [CollatzResearch.WordTrace]
  refine ⟨67162287353839190197253729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44774858235892793464835819 67162287353839190197253729)
  ·
    refine ⟨50371715515379392647940297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67162287353839190197253729 50371715515379392647940297)
    ·
      refine ⟨37778786636534544485955223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50371715515379392647940297 37778786636534544485955223)
      ·
        refine ⟨56668179954801816728932835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37778786636534544485955223 56668179954801816728932835)
        ·
          refine ⟨85002269932202725093399253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56668179954801816728932835 85002269932202725093399253)
          ·
            refine ⟨1992240701536001369376545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 85002269932202725093399253 1992240701536001369376545)
            ·
              refine ⟨1494180526152001027032409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1992240701536001369376545 1494180526152001027032409)
              ·
                refine ⟨1120635394614000770274307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1494180526152001027032409 1120635394614000770274307)
                ·
                  refine ⟨1680953091921001155411461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1120635394614000770274307 1680953091921001155411461)
                  ·
                    refine ⟨315178704735187716639649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1680953091921001155411461 315178704735187716639649)
                    ·
                      rfl

theorem cell23_1841425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 2, 1, 4].length) (baseStart_1841425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1841425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1841425 prefixEnd_1841425 := by exact prefixLift 1841425
  have htrace : WordTrace (prefixWord ++ tailWord_1841425) baseStart_1841425 baseEnd_1841425 := by
    simpa [prefixWord, tailWord_1841425, baseEnd_1841425] using wordTrace_append hprefix tailTrace_1841425
  have hstable : (prefixWord ++ tailWord_1841425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841425).length < 2 ^ (prefixWord ++ tailWord_1841425).sum := by decide
  have hdescent : baseEnd_1841425 < baseStart_1841425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841427 : List Nat := [1, 1, 1, 2, 1, 3, 1, 2, 2, 4, 5]
def baseStart_1841427 : Nat := 118140960795 + 1841427 * 2 ^ 59
def prefixEnd_1841427 : Nat := 4983230072969 + 3 ^ 40 * 1841427 * 2
def baseEnd_1841427 : Nat := 945537141166872142093937

theorem tailTrace_1841427 : CollatzResearch.WordTrace tailWord_1841427 prefixEnd_1841427 945537141166872142093937 := by
  unfold tailWord_1841427
  simp only [CollatzResearch.WordTrace]
  refine ⟨67162360299831944538826535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44774906866554629692551023 67162360299831944538826535)
  ·
    refine ⟨100743540449747916808239803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67162360299831944538826535 100743540449747916808239803)
    ·
      refine ⟨151115310674621875212359705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100743540449747916808239803 151115310674621875212359705)
      ·
        refine ⟨113336483005966406409269779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151115310674621875212359705 113336483005966406409269779)
        ·
          refine ⟨170004724508949609613904669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113336483005966406409269779 170004724508949609613904669)
          ·
            refine ⟨63751771690856103605214251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170004724508949609613904669 63751771690856103605214251)
            ·
              refine ⟨95627657536284155407821377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63751771690856103605214251 95627657536284155407821377)
              ·
                refine ⟨71720743152213116555866033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95627657536284155407821377 71720743152213116555866033)
                ·
                  refine ⟨53790557364159837416899525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71720743152213116555866033 53790557364159837416899525)
                  ·
                    refine ⟨10085729505779969515668661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53790557364159837416899525 10085729505779969515668661)
                    ·
                      refine ⟨945537141166872142093937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10085729505779969515668661 945537141166872142093937)
                      ·
                        rfl

theorem cell23_1841427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4, 5].length) (baseStart_1841427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1841427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1841427 prefixEnd_1841427 := by exact prefixLift 1841427
  have htrace : WordTrace (prefixWord ++ tailWord_1841427) baseStart_1841427 baseEnd_1841427 := by
    simpa [prefixWord, tailWord_1841427, baseEnd_1841427] using wordTrace_append hprefix tailTrace_1841427
  have hstable : (prefixWord ++ tailWord_1841427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841427).length < 2 ^ (prefixWord ++ tailWord_1841427).sum := by decide
  have hdescent : baseEnd_1841427 < baseStart_1841427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841438 : List Nat := [4, 3, 2, 1, 1, 1, 2, 3, 6]
def baseStart_1841438 : Nat := 118140960795 + 1841438 * 2 ^ 59
def prefixEnd_1841438 : Nat := 4983230072969 + 3 ^ 40 * 1841438 * 2
def baseEnd_1841438 : Nat := 105060309939341288784043

theorem tailTrace_1841438 : CollatzResearch.WordTrace tailWord_1841438 prefixEnd_1841438 105060309939341288784043 := by
  unfold tailWord_1841438
  simp only [CollatzResearch.WordTrace]
  refine ⟨8395345187849011677184621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44775174335194728944984645 8395345187849011677184621)
  ·
    refine ⟨3148254445443379378944233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8395345187849011677184621 3148254445443379378944233)
    ·
      refine ⟨2361190834082534534208175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3148254445443379378944233 2361190834082534534208175)
      ·
        refine ⟨3541786251123801801312263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2361190834082534534208175 3541786251123801801312263)
        ·
          refine ⟨5312679376685702701968395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3541786251123801801312263 5312679376685702701968395)
          ·
            refine ⟨7969019065028554052952593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5312679376685702701968395 7969019065028554052952593)
            ·
              refine ⟨5976764298771415539714445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7969019065028554052952593 5976764298771415539714445)
              ·
                refine ⟨2241286612039280827392917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5976764298771415539714445 2241286612039280827392917)
                ·
                  refine ⟨105060309939341288784043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2241286612039280827392917 105060309939341288784043)
                  ·
                    rfl

theorem cell23_1841438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_1841438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1841438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1841438 prefixEnd_1841438 := by exact prefixLift 1841438
  have htrace : WordTrace (prefixWord ++ tailWord_1841438) baseStart_1841438 baseEnd_1841438 := by
    simpa [prefixWord, tailWord_1841438, baseEnd_1841438] using wordTrace_append hprefix tailTrace_1841438
  have hstable : (prefixWord ++ tailWord_1841438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841438).length < 2 ^ (prefixWord ++ tailWord_1841438).sum := by decide
  have hdescent : baseEnd_1841438 < baseStart_1841438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841441 : List Nat := [1, 2, 3, 2, 1, 1, 2, 2, 4, 3, 2]
def baseStart_1841441 : Nat := 118140960795 + 1841441 * 2 ^ 59
def prefixEnd_1841441 : Nat := 4983230072969 + 3 ^ 40 * 1841441 * 2
def baseEnd_1841441 : Nat := 945544329896035087318873

theorem tailTrace_1841441 : CollatzResearch.WordTrace tailWord_1841441 prefixEnd_1841441 945544329896035087318873 := by
  unfold tailWord_1841441
  simp only [CollatzResearch.WordTrace]
  refine ⟨67162870921781224929836177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44775247281187483286557451 67162870921781224929836177)
  ·
    refine ⟨50372153191335918697377133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67162870921781224929836177 50372153191335918697377133)
    ·
      refine ⟨18889557446750969511516425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50372153191335918697377133 18889557446750969511516425)
      ·
        refine ⟨14167168085063227133637319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18889557446750969511516425 14167168085063227133637319)
        ·
          refine ⟨21250752127594840700455979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14167168085063227133637319 21250752127594840700455979)
          ·
            refine ⟨31876128191392261050683969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21250752127594840700455979 31876128191392261050683969)
            ·
              refine ⟨23907096143544195788012977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31876128191392261050683969 23907096143544195788012977)
              ·
                refine ⟨17930322107658146841009733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23907096143544195788012977 17930322107658146841009733)
                ·
                  refine ⟨3361935395185902532689325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17930322107658146841009733 3361935395185902532689325)
                  ·
                    refine ⟨1260725773194713449758497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3361935395185902532689325 1260725773194713449758497)
                    ·
                      refine ⟨945544329896035087318873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1260725773194713449758497 945544329896035087318873)
                      ·
                        rfl

theorem cell23_1841441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 4, 3, 2].length) (baseStart_1841441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1841441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1841441 prefixEnd_1841441 := by exact prefixLift 1841441
  have htrace : WordTrace (prefixWord ++ tailWord_1841441) baseStart_1841441 baseEnd_1841441 := by
    simpa [prefixWord, tailWord_1841441, baseEnd_1841441] using wordTrace_append hprefix tailTrace_1841441
  have hstable : (prefixWord ++ tailWord_1841441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841441).length < 2 ^ (prefixWord ++ tailWord_1841441).sum := by decide
  have hdescent : baseEnd_1841441 < baseStart_1841441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841458 : List Nat := [3, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2]
def baseStart_1841458 : Nat := 118140960795 + 1841458 * 2 ^ 59
def prefixEnd_1841458 : Nat := 4983230072969 + 3 ^ 40 * 1841458 * 2
def baseEnd_1841458 : Nat := 945553059067161520806295

theorem tailTrace_1841458 : CollatzResearch.WordTrace tailWord_1841458 prefixEnd_1841458 945553059067161520806295 := by
  unfold tailWord_1841458
  simp only [CollatzResearch.WordTrace]
  refine ⟨16790872740679909208301257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44775660641813091222136685 16790872740679909208301257)
  ·
    refine ⟨12593154555509931906225943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16790872740679909208301257 12593154555509931906225943)
    ·
      refine ⟨18889731833264897859338915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12593154555509931906225943 18889731833264897859338915)
      ·
        refine ⟨28334597749897346789008373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18889731833264897859338915 28334597749897346789008373)
        ·
          refine ⟨2656368539052876261469535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28334597749897346789008373 2656368539052876261469535)
          ·
            refine ⟨3984552808579314392204303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2656368539052876261469535 3984552808579314392204303)
            ·
              refine ⟨5976829212868971588306455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3984552808579314392204303 5976829212868971588306455)
              ·
                refine ⟨8965243819303457382459683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5976829212868971588306455 8965243819303457382459683)
                ·
                  refine ⟨13447865728955186073689525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8965243819303457382459683 13447865728955186073689525)
                  ·
                    refine ⟨1260737412089548694408393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13447865728955186073689525 1260737412089548694408393)
                    ·
                      refine ⟨945553059067161520806295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1260737412089548694408393 945553059067161520806295)
                      ·
                        rfl

theorem cell23_1841458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2].length) (baseStart_1841458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1841458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1841458 prefixEnd_1841458 := by exact prefixLift 1841458
  have htrace : WordTrace (prefixWord ++ tailWord_1841458) baseStart_1841458 baseEnd_1841458 := by
    simpa [prefixWord, tailWord_1841458, baseEnd_1841458] using wordTrace_append hprefix tailTrace_1841458
  have hstable : (prefixWord ++ tailWord_1841458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841458).length < 2 ^ (prefixWord ++ tailWord_1841458).sum := by decide
  have hdescent : baseEnd_1841458 < baseStart_1841458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841464 : List Nat := [2, 1, 2, 1, 3, 1, 4, 2, 1, 6]
def baseStart_1841464 : Nat := 118140960795 + 1841464 * 2 ^ 59
def prefixEnd_1841464 : Nat := 4983230072969 + 3 ^ 40 * 1841464 * 2
def baseEnd_1841464 : Nat := 315185379983696165777089

theorem tailTrace_1841464 : CollatzResearch.WordTrace tailWord_1841464 prefixEnd_1841464 315185379983696165777089 := by
  unfold tailWord_1841464
  simp only [CollatzResearch.WordTrace]
  refine ⟨33581854900348949928961723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44775806533798599905282297 33581854900348949928961723)
  ·
    refine ⟨50372782350523424893442585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33581854900348949928961723 50372782350523424893442585)
    ·
      refine ⟨37779586762892568670081939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50372782350523424893442585 37779586762892568670081939)
      ·
        refine ⟨56669380144338853005122909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37779586762892568670081939 56669380144338853005122909)
        ·
          refine ⟨21251017554127069876921091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56669380144338853005122909 21251017554127069876921091)
          ·
            refine ⟨31876526331190604815381637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21251017554127069876921091 31876526331190604815381637)
            ·
              refine ⟨5976848687098238402884057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31876526331190604815381637 5976848687098238402884057)
              ·
                refine ⟨4482636515323678802163043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5976848687098238402884057 4482636515323678802163043)
                ·
                  refine ⟨6723954772985518203244565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4482636515323678802163043 6723954772985518203244565)
                  ·
                    refine ⟨315185379983696165777089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6723954772985518203244565 315185379983696165777089)
                    ·
                      rfl

theorem cell23_1841464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2, 1, 6].length) (baseStart_1841464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1841464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1841464 prefixEnd_1841464 := by exact prefixLift 1841464
  have htrace : WordTrace (prefixWord ++ tailWord_1841464) baseStart_1841464 baseEnd_1841464 := by
    simpa [prefixWord, tailWord_1841464, baseEnd_1841464] using wordTrace_append hprefix tailTrace_1841464
  have hstable : (prefixWord ++ tailWord_1841464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841464).length < 2 ^ (prefixWord ++ tailWord_1841464).sum := by decide
  have hdescent : baseEnd_1841464 < baseStart_1841464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841465 : List Nat := [1, 2, 1, 6, 1, 1, 1, 5, 1, 1, 3]
def baseStart_1841465 : Nat := 118140960795 + 1841465 * 2 ^ 59
def prefixEnd_1841465 : Nat := 4983230072969 + 3 ^ 40 * 1841465 * 2
def baseEnd_1841465 : Nat := 945556653431742993418763

theorem tailTrace_1841465 : CollatzResearch.WordTrace tailWord_1841465 prefixEnd_1841465 945556653431742993418763 := by
  unfold tailWord_1841465
  simp only [CollatzResearch.WordTrace]
  refine ⟨67163746273694277028709849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44775830849129518019139899 67163746273694277028709849)
  ·
    refine ⟨50372809705270707771532387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67163746273694277028709849 50372809705270707771532387)
    ·
      refine ⟨75559214557906061657298581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50372809705270707771532387 75559214557906061657298581)
      ·
        refine ⟨3541838182401846640185871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 75559214557906061657298581 3541838182401846640185871)
        ·
          refine ⟨5312757273602769960278807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3541838182401846640185871 5312757273602769960278807)
          ·
            refine ⟨7969135910404154940418211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5312757273602769960278807 7969135910404154940418211)
            ·
              refine ⟨11953703865606232410627317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7969135910404154940418211 11953703865606232410627317)
              ·
                refine ⟨1120659737400584288496311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11953703865606232410627317 1120659737400584288496311)
                ·
                  refine ⟨1680989606100876432744467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1120659737400584288496311 1680989606100876432744467)
                  ·
                    refine ⟨2521484409151314649116701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1680989606100876432744467 2521484409151314649116701)
                    ·
                      refine ⟨945556653431742993418763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2521484409151314649116701 945556653431742993418763)
                      ·
                        rfl

theorem cell23_1841465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_1841465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1841465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1841465 prefixEnd_1841465 := by exact prefixLift 1841465
  have htrace : WordTrace (prefixWord ++ tailWord_1841465) baseStart_1841465 baseEnd_1841465 := by
    simpa [prefixWord, tailWord_1841465, baseEnd_1841465] using wordTrace_append hprefix tailTrace_1841465
  have hstable : (prefixWord ++ tailWord_1841465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841465).length < 2 ^ (prefixWord ++ tailWord_1841465).sum := by decide
  have hdescent : baseEnd_1841465 < baseStart_1841465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841471 : List Nat := [1, 1, 2, 2, 4, 1, 3, 3, 1, 1, 4]
def baseStart_1841471 : Nat := 118140960795 + 1841471 * 2 ^ 59
def prefixEnd_1841471 : Nat := 4983230072969 + 3 ^ 40 * 1841471 * 2
def baseEnd_1841471 : Nat := 945559734315669969943735

theorem tailTrace_1841471 : CollatzResearch.WordTrace tailWord_1841471 prefixEnd_1841471 945559734315669969943735 := by
  unfold tailWord_1841471
  simp only [CollatzResearch.WordTrace]
  refine ⟨67163965111672540053428267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44775976741115026702285511 67163965111672540053428267)
  ·
    refine ⟨100745947667508810080142401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67163965111672540053428267 100745947667508810080142401)
    ·
      refine ⟨75559460750631607560106801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100745947667508810080142401 75559460750631607560106801)
      ·
        refine ⟨56669595562973705670080101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75559460750631607560106801 56669595562973705670080101)
        ·
          refine ⟨10625549168057569813140019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56669595562973705670080101 10625549168057569813140019)
          ·
            refine ⟨15938323752086354719710029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10625549168057569813140019 15938323752086354719710029)
            ·
              refine ⟨5976871407032383019891261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15938323752086354719710029 5976871407032383019891261)
              ·
                refine ⟨2241326777637143632459223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5976871407032383019891261 2241326777637143632459223)
                ·
                  refine ⟨3361990166455715448688835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2241326777637143632459223 3361990166455715448688835)
                  ·
                    refine ⟨5042985249683573173033253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3361990166455715448688835 5042985249683573173033253)
                    ·
                      refine ⟨945559734315669969943735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5042985249683573173033253 945559734315669969943735)
                      ·
                        rfl

theorem cell23_1841471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 3, 1, 1, 4].length) (baseStart_1841471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1841471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1841471 prefixEnd_1841471 := by exact prefixLift 1841471
  have htrace : WordTrace (prefixWord ++ tailWord_1841471) baseStart_1841471 baseEnd_1841471 := by
    simpa [prefixWord, tailWord_1841471, baseEnd_1841471] using wordTrace_append hprefix tailTrace_1841471
  have hstable : (prefixWord ++ tailWord_1841471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841471).length < 2 ^ (prefixWord ++ tailWord_1841471).sum := by decide
  have hdescent : baseEnd_1841471 < baseStart_1841471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841484 : List Nat := [2, 2, 1, 3, 2, 1, 2, 2, 1, 1, 6]
def baseStart_1841484 : Nat := 118140960795 + 1841484 * 2 ^ 59
def prefixEnd_1841484 : Nat := 4983230072969 + 3 ^ 40 * 1841484 * 2
def baseEnd_1841484 : Nat := 945566409564178419081175

theorem tailTrace_1841484 : CollatzResearch.WordTrace tailWord_1841484 prefixEnd_1841484 945566409564178419081175 := by
  unfold tailWord_1841484
  simp only [CollatzResearch.WordTrace]
  refine ⟨33582219630312721636825753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44776292840416962182434337 33582219630312721636825753)
  ·
    refine ⟨25186664722734541227619315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33582219630312721636825753 25186664722734541227619315)
    ·
      refine ⟨37779997084101811841428973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25186664722734541227619315 37779997084101811841428973)
      ·
        refine ⟨14167498906538179440535865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37779997084101811841428973 14167498906538179440535865)
        ·
          refine ⟨10625624179903634580401899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14167498906538179440535865 10625624179903634580401899)
          ·
            refine ⟨15938436269855451870602849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10625624179903634580401899 15938436269855451870602849)
            ·
              refine ⟨11953827202391588902952137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15938436269855451870602849 11953827202391588902952137)
              ·
                refine ⟨8965370401793691677214103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11953827202391588902952137 8965370401793691677214103)
                ·
                  refine ⟨13448055602690537515821155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8965370401793691677214103 13448055602690537515821155)
                  ·
                    refine ⟨20172083404035806273731733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13448055602690537515821155 20172083404035806273731733)
                    ·
                      refine ⟨945566409564178419081175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20172083404035806273731733 945566409564178419081175)
                      ·
                        rfl

theorem cell23_1841484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_1841484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1841484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1841484 prefixEnd_1841484 := by exact prefixLift 1841484
  have htrace : WordTrace (prefixWord ++ tailWord_1841484) baseStart_1841484 baseEnd_1841484 := by
    simpa [prefixWord, tailWord_1841484, baseEnd_1841484] using wordTrace_append hprefix tailTrace_1841484
  have hstable : (prefixWord ++ tailWord_1841484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841484).length < 2 ^ (prefixWord ++ tailWord_1841484).sum := by decide
  have hdescent : baseEnd_1841484 < baseStart_1841484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841488 : List Nat := [2, 1, 1, 1, 1, 6, 1, 3, 3, 2, 2]
def baseStart_1841488 : Nat := 118140960795 + 1841488 * 2 ^ 59
def prefixEnd_1841488 : Nat := 4983230072969 + 3 ^ 40 * 1841488 * 2
def baseEnd_1841488 : Nat := 945568463486796403431157

theorem tailTrace_1841488 : CollatzResearch.WordTrace tailWord_1841488 prefixEnd_1841488 945568463486796403431157 := by
  unfold tailWord_1841488
  simp only [CollatzResearch.WordTrace]
  refine ⟨33582292576305475978398559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44776390101740634637864745 33582292576305475978398559)
  ·
    refine ⟨50373438864458213967597839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33582292576305475978398559 50373438864458213967597839)
    ·
      refine ⟨75560158296687320951396759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50373438864458213967597839 75560158296687320951396759)
      ·
        refine ⟨113340237445030981427095139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75560158296687320951396759 113340237445030981427095139)
        ·
          refine ⟨170010356167546472140642709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113340237445030981427095139 170010356167546472140642709)
          ·
            refine ⟨7969235445353740881592627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 170010356167546472140642709 7969235445353740881592627)
            ·
              refine ⟨11953853168030611322388941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7969235445353740881592627 11953853168030611322388941)
              ·
                refine ⟨4482694938011479245895853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11953853168030611322388941 4482694938011479245895853)
                ·
                  refine ⟨1681010601754304717210945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4482694938011479245895853 1681010601754304717210945)
                  ·
                    refine ⟨1260757951315728537908209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1681010601754304717210945 1260757951315728537908209)
                    ·
                      refine ⟨945568463486796403431157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1260757951315728537908209 945568463486796403431157)
                      ·
                        rfl

theorem cell23_1841488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3, 3, 2, 2].length) (baseStart_1841488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1841488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1841488 prefixEnd_1841488 := by exact prefixLift 1841488
  have htrace : WordTrace (prefixWord ++ tailWord_1841488) baseStart_1841488 baseEnd_1841488 := by
    simpa [prefixWord, tailWord_1841488, baseEnd_1841488] using wordTrace_append hprefix tailTrace_1841488
  have hstable : (prefixWord ++ tailWord_1841488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841488).length < 2 ^ (prefixWord ++ tailWord_1841488).sum := by decide
  have hdescent : baseEnd_1841488 < baseStart_1841488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841508 : List Nat := [2, 3, 1, 1, 3, 1, 4, 2, 1, 2, 3]
def baseStart_1841508 : Nat := 118140960795 + 1841508 * 2 ^ 59
def prefixEnd_1841508 : Nat := 4983230072969 + 3 ^ 40 * 1841508 * 2
def baseEnd_1841508 : Nat := 945578733099886325181065

theorem tailTrace_1841508 : CollatzResearch.WordTrace tailWord_1841508 prefixEnd_1841508 945578733099886325181065 := by
  unfold tailWord_1841508
  simp only [CollatzResearch.WordTrace]
  refine ⟨33582657306269247686262589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44776876408358996915016785 33582657306269247686262589)
  ·
    refine ⟨12593496489850967882348471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33582657306269247686262589 12593496489850967882348471)
    ·
      refine ⟨18890244734776451823522707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12593496489850967882348471 18890244734776451823522707)
      ·
        refine ⟨28335367102164677735284061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18890244734776451823522707 28335367102164677735284061)
        ·
          refine ⟨10625762663311754150731523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28335367102164677735284061 10625762663311754150731523)
          ·
            refine ⟨15938643994967631226097285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10625762663311754150731523 15938643994967631226097285)
            ·
              refine ⟨2988495749056430854893241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15938643994967631226097285 2988495749056430854893241)
              ·
                refine ⟨2241371811792323141169931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2988495749056430854893241 2241371811792323141169931)
                ·
                  refine ⟨3362057717688484711754897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2241371811792323141169931 3362057717688484711754897)
                  ·
                    refine ⟨2521543288266363533816173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3362057717688484711754897 2521543288266363533816173)
                    ·
                      refine ⟨945578733099886325181065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2521543288266363533816173 945578733099886325181065)
                      ·
                        rfl

theorem cell23_1841508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 2, 1, 2, 3].length) (baseStart_1841508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1841508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1841508 prefixEnd_1841508 := by exact prefixLift 1841508
  have htrace : WordTrace (prefixWord ++ tailWord_1841508) baseStart_1841508 baseEnd_1841508 := by
    simpa [prefixWord, tailWord_1841508, baseEnd_1841508] using wordTrace_append hprefix tailTrace_1841508
  have hstable : (prefixWord ++ tailWord_1841508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841508).length < 2 ^ (prefixWord ++ tailWord_1841508).sum := by decide
  have hdescent : baseEnd_1841508 < baseStart_1841508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841511 : List Nat := [1, 1, 5, 1, 3, 1, 4, 7]
def baseStart_1841511 : Nat := 118140960795 + 1841511 * 2 ^ 59
def prefixEnd_1841511 : Nat := 4983230072969 + 3 ^ 40 * 1841511 * 2
def baseEnd_1841511 : Nat := 35021491612661104201613

theorem tailTrace_1841511 : CollatzResearch.WordTrace tailWord_1841511 prefixEnd_1841511 35021491612661104201613 := by
  unfold tailWord_1841511
  simp only [CollatzResearch.WordTrace]
  refine ⟨67165424031527626884884387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44776949354351751256589591 67165424031527626884884387)
  ·
    refine ⟨100748136047291440327326581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67165424031527626884884387 100748136047291440327326581)
    ·
      refine ⟨9445137754433572530686867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100748136047291440327326581 9445137754433572530686867)
      ·
        refine ⟨14167706631650358796030301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9445137754433572530686867 14167706631650358796030301)
        ·
          refine ⟨5312889986868884548511363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14167706631650358796030301 5312889986868884548511363)
          ·
            refine ⟨7969334980303326822767045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5312889986868884548511363 7969334980303326822767045)
            ·
              refine ⟨1494250308806873779268821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7969334980303326822767045 1494250308806873779268821)
              ·
                refine ⟨35021491612661104201613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1494250308806873779268821 35021491612661104201613)
                ·
                  rfl

theorem cell23_1841511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 7].length) (baseStart_1841511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1841511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1841511 prefixEnd_1841511 := by exact prefixLift 1841511
  have htrace : WordTrace (prefixWord ++ tailWord_1841511) baseStart_1841511 baseEnd_1841511 := by
    simpa [prefixWord, tailWord_1841511, baseEnd_1841511] using wordTrace_append hprefix tailTrace_1841511
  have hstable : (prefixWord ++ tailWord_1841511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841511).length < 2 ^ (prefixWord ++ tailWord_1841511).sum := by decide
  have hdescent : baseEnd_1841511 < baseStart_1841511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841522 : List Nat := [3, 2, 1, 2, 1, 3, 3, 3, 1, 2, 2]
def baseStart_1841522 : Nat := 118140960795 + 1841522 * 2 ^ 59
def prefixEnd_1841522 : Nat := 4983230072969 + 3 ^ 40 * 1841522 * 2
def baseEnd_1841522 : Nat := 945585921829049270406001

theorem tailTrace_1841522 : CollatzResearch.WordTrace tailWord_1841522 prefixEnd_1841522 945585921829049270406001 := by
  unfold tailWord_1841522
  simp only [CollatzResearch.WordTrace]
  refine ⟨16791456308621943940883705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44777216822991850509023213 16791456308621943940883705)
  ·
    refine ⟨12593592231466457955662779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16791456308621943940883705 12593592231466457955662779)
    ·
      refine ⟨18890388347199686933494169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12593592231466457955662779 18890388347199686933494169)
      ·
        refine ⟨14167791260399765200120627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18890388347199686933494169 14167791260399765200120627)
        ·
          refine ⟨21251686890599647800180941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14167791260399765200120627 21251686890599647800180941)
          ·
            refine ⟨7969382583974867925067853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21251686890599647800180941 7969382583974867925067853)
            ·
              refine ⟨2988518468990575471900445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7969382583974867925067853 2988518468990575471900445)
              ·
                refine ⟨1120694425871465801962667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2988518468990575471900445 1120694425871465801962667)
                ·
                  refine ⟨1681041638807198702944001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1120694425871465801962667 1681041638807198702944001)
                  ·
                    refine ⟨1260781229105399027208001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1681041638807198702944001 1260781229105399027208001)
                    ·
                      refine ⟨945585921829049270406001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1260781229105399027208001 945585921829049270406001)
                      ·
                        rfl

theorem cell23_1841522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 3, 1, 2, 2].length) (baseStart_1841522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1841522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1841522 prefixEnd_1841522 := by exact prefixLift 1841522
  have htrace : WordTrace (prefixWord ++ tailWord_1841522) baseStart_1841522 baseEnd_1841522 := by
    simpa [prefixWord, tailWord_1841522, baseEnd_1841522] using wordTrace_append hprefix tailTrace_1841522
  have hstable : (prefixWord ++ tailWord_1841522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841522).length < 2 ^ (prefixWord ++ tailWord_1841522).sum := by decide
  have hdescent : baseEnd_1841522 < baseStart_1841522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841539 : List Nat := [1, 1, 1, 3, 6, 1, 3, 2, 1, 2, 2]
def baseStart_1841539 : Nat := 118140960795 + 1841539 * 2 ^ 59
def prefixEnd_1841539 : Nat := 4983230072969 + 3 ^ 40 * 1841539 * 2
def baseEnd_1841539 : Nat := 945594651000175703893423

theorem tailTrace_1841539 : CollatzResearch.WordTrace tailWord_1841539 prefixEnd_1841539 945594651000175703893423 := by
  unfold tailWord_1841539
  simp only [CollatzResearch.WordTrace]
  refine ⟨67166445275426187666903671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44777630183617458444602447 67166445275426187666903671)
  ·
    refine ⟨100749667913139281500355507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67166445275426187666903671 100749667913139281500355507)
    ·
      refine ⟨151124501869708922250533261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100749667913139281500355507 151124501869708922250533261)
      ·
        refine ⟨56671688201140845843949973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151124501869708922250533261 56671688201140845843949973)
        ·
          refine ⟨2656485384428477148935155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 56671688201140845843949973 2656485384428477148935155)
          ·
            refine ⟨3984728076642715723402733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2656485384428477148935155 3984728076642715723402733)
            ·
              refine ⟨1494273028741018396276025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3984728076642715723402733 1494273028741018396276025)
              ·
                refine ⟨1120704771555763797207019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1494273028741018396276025 1120704771555763797207019)
                ·
                  refine ⟨1681057157333645695810529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1120704771555763797207019 1681057157333645695810529)
                  ·
                    refine ⟨1260792868000234271857897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1681057157333645695810529 1260792868000234271857897)
                    ·
                      refine ⟨945594651000175703893423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1260792868000234271857897 945594651000175703893423)
                      ·
                        rfl

theorem cell23_1841539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 2, 1, 2, 2].length) (baseStart_1841539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1841539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1841539 prefixEnd_1841539 := by exact prefixLift 1841539
  have htrace : WordTrace (prefixWord ++ tailWord_1841539) baseStart_1841539 baseEnd_1841539 := by
    simpa [prefixWord, tailWord_1841539, baseEnd_1841539] using wordTrace_append hprefix tailTrace_1841539
  have hstable : (prefixWord ++ tailWord_1841539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841539).length < 2 ^ (prefixWord ++ tailWord_1841539).sum := by decide
  have hdescent : baseEnd_1841539 < baseStart_1841539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841565 : List Nat := [1, 4, 2, 1, 4, 1, 1, 1, 3, 3, 2]
def baseStart_1841565 : Nat := 118140960795 + 1841565 * 2 ^ 59
def prefixEnd_1841565 : Nat := 4983230072969 + 3 ^ 40 * 1841565 * 2
def baseEnd_1841565 : Nat := 945608001497192602168303

theorem tailTrace_1841565 : CollatzResearch.WordTrace tailWord_1841565 prefixEnd_1841565 945608001497192602168303 := by
  unfold tailWord_1841565
  simp only [CollatzResearch.WordTrace]
  refine ⟨67167393573331994107350149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44778262382221329404900099 67167393573331994107350149)
  ·
    refine ⟨12593886294999748895128153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67167393573331994107350149 12593886294999748895128153)
    ·
      refine ⟨9445414721249811671346115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12593886294999748895128153 9445414721249811671346115)
      ·
        refine ⟨14168122081874717507019173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9445414721249811671346115 14168122081874717507019173)
        ·
          refine ⟨2656522890351509532566095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14168122081874717507019173 2656522890351509532566095)
          ·
            refine ⟨3984784335527264298849143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2656522890351509532566095 3984784335527264298849143)
            ·
              refine ⟨5977176503290896448273715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3984784335527264298849143 5977176503290896448273715)
              ·
                refine ⟨8965764754936344672410573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5977176503290896448273715 8965764754936344672410573)
                ·
                  refine ⟨3362161783101129252153965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8965764754936344672410573 3362161783101129252153965)
                  ·
                    refine ⟨1260810668662923469557737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3362161783101129252153965 1260810668662923469557737)
                    ·
                      refine ⟨945608001497192602168303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1260810668662923469557737 945608001497192602168303)
                      ·
                        rfl

theorem cell23_1841565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 3, 3, 2].length) (baseStart_1841565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1841565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1841565 prefixEnd_1841565 := by exact prefixLift 1841565
  have htrace : WordTrace (prefixWord ++ tailWord_1841565) baseStart_1841565 baseEnd_1841565 := by
    simpa [prefixWord, tailWord_1841565, baseEnd_1841565] using wordTrace_append hprefix tailTrace_1841565
  have hstable : (prefixWord ++ tailWord_1841565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841565).length < 2 ^ (prefixWord ++ tailWord_1841565).sum := by decide
  have hdescent : baseEnd_1841565 < baseStart_1841565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841594 : List Nat := [3, 1, 1, 1, 2, 1, 1, 3, 1, 2, 7]
def baseStart_1841594 : Nat := 118140960795 + 1841594 * 2 ^ 59
def prefixEnd_1841594 : Nat := 4983230072969 + 3 ^ 40 * 1841594 * 2
def baseEnd_1841594 : Nat := 945622892436172988705669

theorem tailTrace_1841594 : CollatzResearch.WordTrace tailWord_1841594 prefixEnd_1841594 945622892436172988705669 := by
  unfold tailWord_1841594
  simp only [CollatzResearch.WordTrace]
  refine ⟨16792112822556733015038959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44778967526817954706770557 16792112822556733015038959)
  ·
    refine ⟨25188169233835099522558439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16792112822556733015038959 25188169233835099522558439)
    ·
      refine ⟨37782253850752649283837659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25188169233835099522558439 37782253850752649283837659)
      ·
        refine ⟨56673380776128973925756489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37782253850752649283837659 56673380776128973925756489)
        ·
          refine ⟨42505035582096730444317367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56673380776128973925756489 42505035582096730444317367)
          ·
            refine ⟨63757553373145095666476051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42505035582096730444317367 63757553373145095666476051)
            ·
              refine ⟨95636330059717643499714077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63757553373145095666476051 95636330059717643499714077)
              ·
                refine ⟨35863623772394116312392779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95636330059717643499714077 35863623772394116312392779)
                ·
                  refine ⟨53795435658591174468589169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35863623772394116312392779 53795435658591174468589169)
                  ·
                    refine ⟨40346576743943380851441877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53795435658591174468589169 40346576743943380851441877)
                    ·
                      refine ⟨945622892436172988705669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 40346576743943380851441877 945622892436172988705669)
                      ·
                        rfl

theorem cell23_1841594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 1, 2, 7].length) (baseStart_1841594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1841594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1841594 prefixEnd_1841594 := by exact prefixLift 1841594
  have htrace : WordTrace (prefixWord ++ tailWord_1841594) baseStart_1841594 baseEnd_1841594 := by
    simpa [prefixWord, tailWord_1841594, baseEnd_1841594] using wordTrace_append hprefix tailTrace_1841594
  have hstable : (prefixWord ++ tailWord_1841594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841594).length < 2 ^ (prefixWord ++ tailWord_1841594).sum := by decide
  have hdescent : baseEnd_1841594 < baseStart_1841594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841631 : List Nat := [1, 1, 2, 3, 3, 3, 1, 1, 1, 7]
def baseStart_1841631 : Nat := 118140960795 + 1841631 * 2 ^ 59
def prefixEnd_1841631 : Nat := 4983230072969 + 3 ^ 40 * 1841631 * 2
def baseEnd_1841631 : Nat := 315213963740129781314333

theorem tailTrace_1841631 : CollatzResearch.WordTrace tailWord_1841631 prefixEnd_1841631 315213963740129781314333 := by
  unfold tailWord_1841631
  simp only [CollatzResearch.WordTrace]
  refine ⟨67169800791092887379252747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44779867194061924919501831 67169800791092887379252747)
  ·
    refine ⟨100754701186639331068879121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67169800791092887379252747 100754701186639331068879121)
    ·
      refine ⟨75566025889979498301659341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100754701186639331068879121 75566025889979498301659341)
      ·
        refine ⟨28337259708742311863122253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75566025889979498301659341 28337259708742311863122253)
        ·
          refine ⟨10626472390778366948670845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28337259708742311863122253 10626472390778366948670845)
          ·
            refine ⟨3984927146541887605751567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10626472390778366948670845 3984927146541887605751567)
            ·
              refine ⟨5977390719812831408627351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3984927146541887605751567 5977390719812831408627351)
              ·
                refine ⟨8966086079719247112941027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5977390719812831408627351 8966086079719247112941027)
                ·
                  refine ⟨13449129119578870669411541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8966086079719247112941027 13449129119578870669411541)
                  ·
                    refine ⟨315213963740129781314333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13449129119578870669411541 315213963740129781314333)
                    ·
                      rfl

theorem cell23_1841631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 7].length) (baseStart_1841631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1841631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1841631 prefixEnd_1841631 := by exact prefixLift 1841631
  have htrace : WordTrace (prefixWord ++ tailWord_1841631) baseStart_1841631 baseEnd_1841631 := by
    simpa [prefixWord, tailWord_1841631, baseEnd_1841631] using wordTrace_append hprefix tailTrace_1841631
  have hstable : (prefixWord ++ tailWord_1841631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841631).length < 2 ^ (prefixWord ++ tailWord_1841631).sum := by decide
  have hdescent : baseEnd_1841631 < baseStart_1841631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841635 : List Nat := [1, 1, 1, 6, 3, 1, 2, 3, 5]
def baseStart_1841635 : Nat := 118140960795 + 1841635 * 2 ^ 59
def prefixEnd_1841635 : Nat := 4983230072969 + 3 ^ 40 * 1841635 * 2
def baseEnd_1841635 : Nat := 105071549460334147588109

theorem tailTrace_1841635 : CollatzResearch.WordTrace tailWord_1841635 prefixEnd_1841635 105071549460334147588109 := by
  unfold tailWord_1841635
  simp only [CollatzResearch.WordTrace]
  refine ⟨67169946683078396062398359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44779964455385597374932239 67169946683078396062398359)
  ·
    refine ⟨100754920024617594093597539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67169946683078396062398359 100754920024617594093597539)
    ·
      refine ⟨151132380036926391140396309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100754920024617594093597539 151132380036926391140396309)
      ·
        refine ⟨7084330314230924584706077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 151132380036926391140396309 7084330314230924584706077)
        ·
          refine ⟨2656623867836596719264779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7084330314230924584706077 2656623867836596719264779)
          ·
            refine ⟨3984935801754895078897169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2656623867836596719264779 3984935801754895078897169)
            ·
              refine ⟨2988701851316171309172877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3984935801754895078897169 2988701851316171309172877)
              ·
                refine ⟨1120763194243564240939829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2988701851316171309172877 1120763194243564240939829)
                ·
                  refine ⟨105071549460334147588109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1120763194243564240939829 105071549460334147588109)
                  ·
                    rfl

theorem cell23_1841635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 3, 5].length) (baseStart_1841635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1841635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1841635 prefixEnd_1841635 := by exact prefixLift 1841635
  have htrace : WordTrace (prefixWord ++ tailWord_1841635) baseStart_1841635 baseEnd_1841635 := by
    simpa [prefixWord, tailWord_1841635, baseEnd_1841635] using wordTrace_append hprefix tailTrace_1841635
  have hstable : (prefixWord ++ tailWord_1841635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841635).length < 2 ^ (prefixWord ++ tailWord_1841635).sum := by decide
  have hdescent : baseEnd_1841635 < baseStart_1841635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841651 : List Nat := [1, 1, 1, 2, 2, 2, 4, 1, 4, 1, 4]
def baseStart_1841651 : Nat := 118140960795 + 1841651 * 2 ^ 59
def prefixEnd_1841651 : Nat := 4983230072969 + 3 ^ 40 * 1841651 * 2
def baseEnd_1841651 : Nat := 945652160833479265692907

theorem tailTrace_1841651 : CollatzResearch.WordTrace tailWord_1841651 prefixEnd_1841651 945652160833479265692907 := by
  unfold tailWord_1841651
  simp only [CollatzResearch.WordTrace]
  refine ⟨67170530251020430794980807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44780353500680287196653871 67170530251020430794980807)
  ·
    refine ⟨100755795376530646192471211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67170530251020430794980807 100755795376530646192471211)
    ·
      refine ⟨151133693064795969288706817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100755795376530646192471211 151133693064795969288706817)
      ·
        refine ⟨113350269798596976966530113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151133693064795969288706817 113350269798596976966530113)
        ·
          refine ⟨85012702348947732724897585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113350269798596976966530113 85012702348947732724897585)
          ·
            refine ⟨63759526761710799543673189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85012702348947732724897585 63759526761710799543673189)
            ·
              refine ⟨11954911267820774914438723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63759526761710799543673189 11954911267820774914438723)
              ·
                refine ⟨17932366901731162371658085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11954911267820774914438723 17932366901731162371658085)
                ·
                  refine ⟨3362318794074592944685891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17932366901731162371658085 3362318794074592944685891)
                  ·
                    refine ⟨5043478191111889417028837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3362318794074592944685891 5043478191111889417028837)
                    ·
                      refine ⟨945652160833479265692907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5043478191111889417028837 945652160833479265692907)
                      ·
                        rfl

theorem cell23_1841651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 4, 1, 4].length) (baseStart_1841651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1841651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1841651 prefixEnd_1841651 := by exact prefixLift 1841651
  have htrace : WordTrace (prefixWord ++ tailWord_1841651) baseStart_1841651 baseEnd_1841651 := by
    simpa [prefixWord, tailWord_1841651, baseEnd_1841651] using wordTrace_append hprefix tailTrace_1841651
  have hstable : (prefixWord ++ tailWord_1841651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841651).length < 2 ^ (prefixWord ++ tailWord_1841651).sum := by decide
  have hdescent : baseEnd_1841651 < baseStart_1841651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841668 : List Nat := [2, 3, 2, 3, 1, 1, 1, 2, 1, 3, 4]
def baseStart_1841668 : Nat := 118140960795 + 1841668 * 2 ^ 59
def prefixEnd_1841668 : Nat := 4983230072969 + 3 ^ 40 * 1841668 * 2
def baseEnd_1841668 : Nat := 945660890004605699180329

theorem tailTrace_1841668 : CollatzResearch.WordTrace tailWord_1841668 prefixEnd_1841668 945660890004605699180329 := by
  unfold tailWord_1841668
  simp only [CollatzResearch.WordTrace]
  refine ⟨33585575145979421349174829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44780766861305895132233105 33585575145979421349174829)
  ·
    refine ⟨12594590679742283005940561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33585575145979421349174829 12594590679742283005940561)
    ·
      refine ⟨9445943009806712254455421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12594590679742283005940561 9445943009806712254455421)
      ·
        refine ⟨3542228628677517095420783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9445943009806712254455421 3542228628677517095420783)
        ·
          refine ⟨5313342943016275643131175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3542228628677517095420783 5313342943016275643131175)
          ·
            refine ⟨7970014414524413464696763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5313342943016275643131175 7970014414524413464696763)
            ·
              refine ⟨11955021621786620197045145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7970014414524413464696763 11955021621786620197045145)
              ·
                refine ⟨8966266216339965147783859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11955021621786620197045145 8966266216339965147783859)
                ·
                  refine ⟨13449399324509947721675789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8966266216339965147783859 13449399324509947721675789)
                  ·
                    refine ⟨5043524746691230395628421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13449399324509947721675789 5043524746691230395628421)
                    ·
                      refine ⟨945660890004605699180329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5043524746691230395628421 945660890004605699180329)
                      ·
                        rfl

theorem cell23_1841668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_1841668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1841668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1841668 prefixEnd_1841668 := by exact prefixLift 1841668
  have htrace : WordTrace (prefixWord ++ tailWord_1841668) baseStart_1841668 baseEnd_1841668 := by
    simpa [prefixWord, tailWord_1841668, baseEnd_1841668] using wordTrace_append hprefix tailTrace_1841668
  have hstable : (prefixWord ++ tailWord_1841668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841668).length < 2 ^ (prefixWord ++ tailWord_1841668).sum := by decide
  have hdescent : baseEnd_1841668 < baseStart_1841668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841688 : List Nat := [2, 1, 2, 3, 3, 1, 2, 1, 1, 4, 3]
def baseStart_1841688 : Nat := 118140960795 + 1841688 * 2 ^ 59
def prefixEnd_1841688 : Nat := 4983230072969 + 3 ^ 40 * 1841688 * 2
def baseEnd_1841688 : Nat := 945671159617695620930237

theorem tailTrace_1841688 : CollatzResearch.WordTrace tailWord_1841688 prefixEnd_1841688 945671159617695620930237 := by
  unfold tailWord_1841688
  simp only [CollatzResearch.WordTrace]
  refine ⟨33585939875943193057038859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44781253167924257409385145 33585939875943193057038859)
  ·
    refine ⟨50378909813914789585558289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33585939875943193057038859 50378909813914789585558289)
    ·
      refine ⟨37784182360436092189168717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50378909813914789585558289 37784182360436092189168717)
      ·
        refine ⟨14169068385163534570938269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37784182360436092189168717 14169068385163534570938269)
        ·
          refine ⟨5313400644436325464101851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14169068385163534570938269 5313400644436325464101851)
          ·
            refine ⟨7970100966654488196152777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5313400644436325464101851 7970100966654488196152777)
            ·
              refine ⟨5977575724990866147114583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7970100966654488196152777 5977575724990866147114583)
              ·
                refine ⟨8966363587486299220671875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5977575724990866147114583 8966363587486299220671875)
                ·
                  refine ⟨13449545381229448831007813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8966363587486299220671875 13449545381229448831007813)
                  ·
                    refine ⟨2521789758980521655813965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13449545381229448831007813 2521789758980521655813965)
                    ·
                      refine ⟨945671159617695620930237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2521789758980521655813965 945671159617695620930237)
                      ·
                        rfl

theorem cell23_1841688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_1841688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1841688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1841688 prefixEnd_1841688 := by exact prefixLift 1841688
  have htrace : WordTrace (prefixWord ++ tailWord_1841688) baseStart_1841688 baseEnd_1841688 := by
    simpa [prefixWord, tailWord_1841688, baseEnd_1841688] using wordTrace_append hprefix tailTrace_1841688
  have hstable : (prefixWord ++ tailWord_1841688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841688).length < 2 ^ (prefixWord ++ tailWord_1841688).sum := by decide
  have hdescent : baseEnd_1841688 < baseStart_1841688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841725 : List Nat := [1, 4, 1, 3, 2, 1, 4, 1, 6]
def baseStart_1841725 : Nat := 118140960795 + 1841725 * 2 ^ 59
def prefixEnd_1841725 : Nat := 4983230072969 + 3 ^ 40 * 1841725 * 2
def baseEnd_1841725 : Nat := 105076684266879108463063

theorem tailTrace_1841725 : CollatzResearch.WordTrace tailWord_1841725 prefixEnd_1841725 105076684266879108463063 := by
  unfold tailWord_1841725
  simp only [CollatzResearch.WordTrace]
  refine ⟨67173229252752341433174629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44782152835168227622116419 67173229252752341433174629)
  ·
    refine ⟨12594980484891064018720243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67173229252752341433174629 12594980484891064018720243)
    ·
      refine ⟨18892470727336596028080365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12594980484891064018720243 18892470727336596028080365)
      ·
        refine ⟨7084676522751223510530137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18892470727336596028080365 7084676522751223510530137)
        ·
          refine ⟨5313507392063417632897603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7084676522751223510530137 5313507392063417632897603)
          ·
            refine ⟨7970261088095126449346405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5313507392063417632897603 7970261088095126449346405)
            ·
              refine ⟨1494423954017836209252451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7970261088095126449346405 1494423954017836209252451)
              ·
                refine ⟨2241635931026754313878677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1494423954017836209252451 2241635931026754313878677)
                ·
                  refine ⟨105076684266879108463063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2241635931026754313878677 105076684266879108463063)
                  ·
                    rfl

theorem cell23_1841725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 1, 6].length) (baseStart_1841725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1841725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1841725 prefixEnd_1841725 := by exact prefixLift 1841725
  have htrace : WordTrace (prefixWord ++ tailWord_1841725) baseStart_1841725 baseEnd_1841725 := by
    simpa [prefixWord, tailWord_1841725, baseEnd_1841725] using wordTrace_append hprefix tailTrace_1841725
  have hstable : (prefixWord ++ tailWord_1841725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841725).length < 2 ^ (prefixWord ++ tailWord_1841725).sum := by decide
  have hdescent : baseEnd_1841725 < baseStart_1841725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841728 : List Nat := [2, 1, 1, 2, 2, 2, 2, 1, 3, 5, 2]
def baseStart_1841728 : Nat := 118140960795 + 1841728 * 2 ^ 59
def prefixEnd_1841728 : Nat := 4983230072969 + 3 ^ 40 * 1841728 * 2
def baseEnd_1841728 : Nat := 945691698843875464430053

theorem tailTrace_1841728 : CollatzResearch.WordTrace tailWord_1841728 prefixEnd_1841728 945691698843875464430053 := by
  unfold tailWord_1841728
  simp only [CollatzResearch.WordTrace]
  refine ⟨33586669335870736472766919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44782225781160981963689225 33586669335870736472766919)
  ·
    refine ⟨50380004003806104709150379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33586669335870736472766919 50380004003806104709150379)
    ·
      refine ⟨75570006005709157063725569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50380004003806104709150379 75570006005709157063725569)
      ·
        refine ⟨56677504504281867797794177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75570006005709157063725569 56677504504281867797794177)
        ·
          refine ⟨42508128378211400848345633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56677504504281867797794177 42508128378211400848345633)
          ·
            refine ⟨31881096283658550636259225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42508128378211400848345633 31881096283658550636259225)
            ·
              refine ⟨23910822212743912977194419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31881096283658550636259225 23910822212743912977194419)
              ·
                refine ⟨35866233319115869465791629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23910822212743912977194419 35866233319115869465791629)
                ·
                  refine ⟨13449837494668451049671861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35866233319115869465791629 13449837494668451049671861)
                  ·
                    refine ⟨1260922265125167285906737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13449837494668451049671861 1260922265125167285906737)
                    ·
                      refine ⟨945691698843875464430053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1260922265125167285906737 945691698843875464430053)
                      ·
                        rfl

theorem cell23_1841728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 3, 5, 2].length) (baseStart_1841728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1841728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1841728 prefixEnd_1841728 := by exact prefixLift 1841728
  have htrace : WordTrace (prefixWord ++ tailWord_1841728) baseStart_1841728 baseEnd_1841728 := by
    simpa [prefixWord, tailWord_1841728, baseEnd_1841728] using wordTrace_append hprefix tailTrace_1841728
  have hstable : (prefixWord ++ tailWord_1841728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841728).length < 2 ^ (prefixWord ++ tailWord_1841728).sum := by decide
  have hdescent : baseEnd_1841728 < baseStart_1841728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841738 : List Nat := [3, 1, 2, 1, 1, 5, 1, 1, 3, 5]
def baseStart_1841738 : Nat := 118140960795 + 1841738 * 2 ^ 59
def prefixEnd_1841738 : Nat := 4983230072969 + 3 ^ 40 * 1841738 * 2
def baseEnd_1841738 : Nat := 315232277883473475101669

theorem tailTrace_1841738 : CollatzResearch.WordTrace tailWord_1841738 prefixEnd_1841738 315232277883473475101669 := by
  unfold tailWord_1841738
  simp only [CollatzResearch.WordTrace]
  refine ⟨16793425850426311163349467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44782468934470163102265245 16793425850426311163349467)
  ·
    refine ⟨25190138775639466745024201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16793425850426311163349467 25190138775639466745024201)
    ·
      refine ⟨18892604081729600058768151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25190138775639466745024201 18892604081729600058768151)
      ·
        refine ⟨28338906122594400088152227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18892604081729600058768151 28338906122594400088152227)
        ·
          refine ⟨42508359183891600132228341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28338906122594400088152227 42508359183891600132228341)
          ·
            refine ⟨3985158673489837512396407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42508359183891600132228341 3985158673489837512396407)
            ·
              refine ⟨5977738010234756268594611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3985158673489837512396407 5977738010234756268594611)
              ·
                refine ⟨8966607015352134402891917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5977738010234756268594611 8966607015352134402891917)
                ·
                  refine ⟨3362477630757050401084469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8966607015352134402891917 3362477630757050401084469)
                  ·
                    refine ⟨315232277883473475101669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3362477630757050401084469 315232277883473475101669)
                    ·
                      rfl

theorem cell23_1841738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 3, 5].length) (baseStart_1841738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1841738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1841738 prefixEnd_1841738 := by exact prefixLift 1841738
  have htrace : WordTrace (prefixWord ++ tailWord_1841738) baseStart_1841738 baseEnd_1841738 := by
    simpa [prefixWord, tailWord_1841738, baseEnd_1841738] using wordTrace_append hprefix tailTrace_1841738
  have hstable : (prefixWord ++ tailWord_1841738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841738).length < 2 ^ (prefixWord ++ tailWord_1841738).sum := by decide
  have hdescent : baseEnd_1841738 < baseStart_1841738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841745 : List Nat := [1, 2, 2, 1, 3, 3, 1, 3, 2, 3, 2]
def baseStart_1841745 : Nat := 118140960795 + 1841745 * 2 ^ 59
def prefixEnd_1841745 : Nat := 4983230072969 + 3 ^ 40 * 1841745 * 2
def baseEnd_1841745 : Nat := 945700428015001897917475

theorem tailTrace_1841745 : CollatzResearch.WordTrace tailWord_1841745 prefixEnd_1841745 945700428015001897917475 := by
  unfold tailWord_1841745
  simp only [CollatzResearch.WordTrace]
  refine ⟨67173958712679884848902689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44782639141786589899268459 67173958712679884848902689)
  ·
    refine ⟨50380469034509913636677017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67173958712679884848902689 50380469034509913636677017)
    ·
      refine ⟨37785351775882435227507763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50380469034509913636677017 37785351775882435227507763)
      ·
        refine ⟨56678027663823652841261645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37785351775882435227507763 56678027663823652841261645)
        ·
          refine ⟨21254260373933869815473117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56678027663823652841261645 21254260373933869815473117)
          ·
            refine ⟨7970347640225201180802419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21254260373933869815473117 7970347640225201180802419)
            ·
              refine ⟨11955521460337801771203629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7970347640225201180802419 11955521460337801771203629)
              ·
                refine ⟨4483320547626675664201361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11955521460337801771203629 4483320547626675664201361)
                ·
                  refine ⟨3362490410720006748151021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4483320547626675664201361 3362490410720006748151021)
                  ·
                    refine ⟨1260933904020002530556633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3362490410720006748151021 1260933904020002530556633)
                    ·
                      refine ⟨945700428015001897917475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1260933904020002530556633 945700428015001897917475)
                      ·
                        rfl

theorem cell23_1841745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3, 2, 3, 2].length) (baseStart_1841745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1841745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1841745 prefixEnd_1841745 := by exact prefixLift 1841745
  have htrace : WordTrace (prefixWord ++ tailWord_1841745) baseStart_1841745 baseEnd_1841745 := by
    simpa [prefixWord, tailWord_1841745, baseEnd_1841745] using wordTrace_append hprefix tailTrace_1841745
  have hstable : (prefixWord ++ tailWord_1841745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841745).length < 2 ^ (prefixWord ++ tailWord_1841745).sum := by decide
  have hdescent : baseEnd_1841745 < baseStart_1841745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841771 : List Nat := [1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 6]
def baseStart_1841771 : Nat := 118140960795 + 1841771 * 2 ^ 59
def prefixEnd_1841771 : Nat := 4983230072969 + 3 ^ 40 * 1841771 * 2
def baseEnd_1841771 : Nat := 945713778512018796192355

theorem tailTrace_1841771 : CollatzResearch.WordTrace tailWord_1841771 prefixEnd_1841771 945713778512018796192355 := by
  unfold tailWord_1841771
  simp only [CollatzResearch.WordTrace]
  refine ⟨67174907010585691289349167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44783271340390460859566111 67174907010585691289349167)
  ·
    refine ⟨100762360515878536934023751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67174907010585691289349167 100762360515878536934023751)
    ·
      refine ⟨151143540773817805401035627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100762360515878536934023751 151143540773817805401035627)
      ·
        refine ⟨226715311160726708101553441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151143540773817805401035627 226715311160726708101553441)
        ·
          refine ⟨170036483370545031076165081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226715311160726708101553441 170036483370545031076165081)
          ·
            refine ⟨127527362527908773307123811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170036483370545031076165081 127527362527908773307123811)
            ·
              refine ⟨191291043791863159960685717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127527362527908773307123811 191291043791863159960685717)
              ·
                refine ⟨8966767677743585623157143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 191291043791863159960685717 8966767677743585623157143)
                ·
                  refine ⟨13450151516615378434735715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8966767677743585623157143 13450151516615378434735715)
                  ·
                    refine ⟨20175227274923067652103573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13450151516615378434735715 20175227274923067652103573)
                    ·
                      refine ⟨945713778512018796192355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20175227274923067652103573 945713778512018796192355)
                      ·
                        rfl

theorem cell23_1841771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 6].length) (baseStart_1841771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1841771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1841771 prefixEnd_1841771 := by exact prefixLift 1841771
  have htrace : WordTrace (prefixWord ++ tailWord_1841771) baseStart_1841771 baseEnd_1841771 := by
    simpa [prefixWord, tailWord_1841771, baseEnd_1841771] using wordTrace_append hprefix tailTrace_1841771
  have hstable : (prefixWord ++ tailWord_1841771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841771).length < 2 ^ (prefixWord ++ tailWord_1841771).sum := by decide
  have hdescent : baseEnd_1841771 < baseStart_1841771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841785 : List Nat := [1, 2, 1, 3, 3, 2, 2, 3, 2, 4]
def baseStart_1841785 : Nat := 118140960795 + 1841785 * 2 ^ 59
def prefixEnd_1841785 : Nat := 4983230072969 + 3 ^ 40 * 1841785 * 2
def baseEnd_1841785 : Nat := 315240322413727247139097

theorem tailTrace_1841785 : CollatzResearch.WordTrace tailWord_1841785 prefixEnd_1841785 315240322413727247139097 := by
  unfold tailWord_1841785
  simp only [CollatzResearch.WordTrace]
  refine ⟨67175417632534971680358809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44783611755023314453572539 67175417632534971680358809)
  ·
    refine ⟨50381563224401228760269107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67175417632534971680358809 50381563224401228760269107)
    ·
      refine ⟨75572344836601843140403661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50381563224401228760269107 75572344836601843140403661)
      ·
        refine ⟨28339629313725691177651373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75572344836601843140403661 28339629313725691177651373)
        ·
          refine ⟨10627360992647134191619265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28339629313725691177651373 10627360992647134191619265)
          ·
            refine ⟨7970520744485350643714449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10627360992647134191619265 7970520744485350643714449)
            ·
              refine ⟨5977890558364012982785837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7970520744485350643714449 5977890558364012982785837)
              ·
                refine ⟨2241708959386504868544689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5977890558364012982785837 2241708959386504868544689)
                ·
                  refine ⟨1681281719539878651408517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2241708959386504868544689 1681281719539878651408517)
                  ·
                    refine ⟨315240322413727247139097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1681281719539878651408517 315240322413727247139097)
                    ·
                      rfl

theorem cell23_1841785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 3, 2, 4].length) (baseStart_1841785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1841785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1841785 prefixEnd_1841785 := by exact prefixLift 1841785
  have htrace : WordTrace (prefixWord ++ tailWord_1841785) baseStart_1841785 baseEnd_1841785 := by
    simpa [prefixWord, tailWord_1841785, baseEnd_1841785] using wordTrace_append hprefix tailTrace_1841785
  have hstable : (prefixWord ++ tailWord_1841785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841785).length < 2 ^ (prefixWord ++ tailWord_1841785).sum := by decide
  have hdescent : baseEnd_1841785 < baseStart_1841785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841788 : List Nat := [2, 2, 2, 1, 1, 2, 3, 3, 1, 2, 4]
def baseStart_1841788 : Nat := 118140960795 + 1841788 * 2 ^ 59
def prefixEnd_1841788 : Nat := 4983230072969 + 3 ^ 40 * 1841788 * 2
def baseEnd_1841788 : Nat := 945722507683145229679777

theorem tailTrace_1841788 : CollatzResearch.WordTrace tailWord_1841788 prefixEnd_1841788 945722507683145229679777 := by
  unfold tailWord_1841788
  simp only [CollatzResearch.WordTrace]
  refine ⟨33587763525762051596359009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44783684701016068795145345 33587763525762051596359009)
  ·
    refine ⟨25190822644321538697269257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33587763525762051596359009 25190822644321538697269257)
    ·
      refine ⟨18893116983241154022951943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25190822644321538697269257 18893116983241154022951943)
      ·
        refine ⟨28339675474861731034427915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18893116983241154022951943 28339675474861731034427915)
        ·
          refine ⟨42509513212292596551641873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28339675474861731034427915 42509513212292596551641873)
          ·
            refine ⟨31882134909219447413731405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42509513212292596551641873 31882134909219447413731405)
            ·
              refine ⟨11955800590957292780149277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31882134909219447413731405 11955800590957292780149277)
              ·
                refine ⟨4483425221608984792555979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11955800590957292780149277 4483425221608984792555979)
                ·
                  refine ⟨6725137832413477188833969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4483425221608984792555979 6725137832413477188833969)
                  ·
                    refine ⟨5043853374310107891625477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6725137832413477188833969 5043853374310107891625477)
                    ·
                      refine ⟨945722507683145229679777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5043853374310107891625477 945722507683145229679777)
                      ·
                        rfl

theorem cell23_1841788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3, 1, 2, 4].length) (baseStart_1841788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1841788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1841788 prefixEnd_1841788 := by exact prefixLift 1841788
  have htrace : WordTrace (prefixWord ++ tailWord_1841788) baseStart_1841788 baseEnd_1841788 := by
    simpa [prefixWord, tailWord_1841788, baseEnd_1841788] using wordTrace_append hprefix tailTrace_1841788
  have hstable : (prefixWord ++ tailWord_1841788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841788).length < 2 ^ (prefixWord ++ tailWord_1841788).sum := by decide
  have hdescent : baseEnd_1841788 < baseStart_1841788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841792 : List Nat := [2, 1, 1, 2, 1, 6, 1, 2, 3, 2, 2]
def baseStart_1841792 : Nat := 118140960795 + 1841792 * 2 ^ 59
def prefixEnd_1841792 : Nat := 4983230072969 + 3 ^ 40 * 1841792 * 2
def baseEnd_1841792 : Nat := 945724561605763214029759

theorem tailTrace_1841792 : CollatzResearch.WordTrace tailWord_1841792 prefixEnd_1841792 945724561605763214029759 := by
  unfold tailWord_1841792
  simp only [CollatzResearch.WordTrace]
  refine ⟨33587836471754805937931815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44783781962339741250575753 33587836471754805937931815)
  ·
    refine ⟨50381754707632208906897723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33587836471754805937931815 50381754707632208906897723)
    ·
      refine ⟨75572632061448313360346585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50381754707632208906897723 75572632061448313360346585)
      ·
        refine ⟨56679474046086235020259939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75572632061448313360346585 56679474046086235020259939)
        ·
          refine ⟨85019211069129352530389909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56679474046086235020259939 85019211069129352530389909)
          ·
            refine ⟨3985275518865438399862027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 85019211069129352530389909 3985275518865438399862027)
            ·
              refine ⟨5977913278298157599793041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3985275518865438399862027 5977913278298157599793041)
              ·
                refine ⟨4483434958723618199844781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5977913278298157599793041 4483434958723618199844781)
                ·
                  refine ⟨1681288109521356824941793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4483434958723618199844781 1681288109521356824941793)
                  ·
                    refine ⟨1260966082141017618706345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1681288109521356824941793 1260966082141017618706345)
                    ·
                      refine ⟨945724561605763214029759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1260966082141017618706345 945724561605763214029759)
                      ·
                        rfl

theorem cell23_1841792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 2, 3, 2, 2].length) (baseStart_1841792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1841792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1841792 prefixEnd_1841792 := by exact prefixLift 1841792
  have htrace : WordTrace (prefixWord ++ tailWord_1841792) baseStart_1841792 baseEnd_1841792 := by
    simpa [prefixWord, tailWord_1841792, baseEnd_1841792] using wordTrace_append hprefix tailTrace_1841792
  have hstable : (prefixWord ++ tailWord_1841792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841792).length < 2 ^ (prefixWord ++ tailWord_1841792).sum := by decide
  have hdescent : baseEnd_1841792 < baseStart_1841792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841811 : List Nat := [1, 1, 1, 2, 1, 2, 2, 2, 4, 7]
def baseStart_1841811 : Nat := 118140960795 + 1841811 * 2 ^ 59
def prefixEnd_1841811 : Nat := 4983230072969 + 3 ^ 40 * 1841811 * 2
def baseEnd_1841811 : Nat := 315244772579399546564057

theorem tailTrace_1841811 : CollatzResearch.WordTrace tailWord_1841811 prefixEnd_1841811 315244772579399546564057 := by
  unfold tailWord_1841811
  simp only [CollatzResearch.WordTrace]
  refine ⟨67176365930440778120805287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44784243953627185413870191 67176365930440778120805287)
  ·
    refine ⟨100764548895661167181207931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67176365930440778120805287 100764548895661167181207931)
    ·
      refine ⟨151146823343491750771811897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100764548895661167181207931 151146823343491750771811897)
      ·
        refine ⟨113360117507618813078858923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151146823343491750771811897 113360117507618813078858923)
        ·
          refine ⟨170040176261428219618288385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113360117507618813078858923 170040176261428219618288385)
          ·
            refine ⟨127530132196071164713716289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170040176261428219618288385 127530132196071164713716289)
            ·
              refine ⟨95647599147053373535287217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127530132196071164713716289 95647599147053373535287217)
              ·
                refine ⟨71735699360290030151465413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95647599147053373535287217 71735699360290030151465413)
                ·
                  refine ⟨13450443630054380653399765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71735699360290030151465413 13450443630054380653399765)
                  ·
                    refine ⟨315244772579399546564057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13450443630054380653399765 315244772579399546564057)
                    ·
                      rfl

theorem cell23_1841811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 7].length) (baseStart_1841811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1841811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1841811 prefixEnd_1841811 := by exact prefixLift 1841811
  have htrace : WordTrace (prefixWord ++ tailWord_1841811) baseStart_1841811 baseEnd_1841811 := by
    simpa [prefixWord, tailWord_1841811, baseEnd_1841811] using wordTrace_append hprefix tailTrace_1841811
  have hstable : (prefixWord ++ tailWord_1841811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841811).length < 2 ^ (prefixWord ++ tailWord_1841811).sum := by decide
  have hdescent : baseEnd_1841811 < baseStart_1841811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841846 : List Nat := [5, 1, 3, 1, 2, 1, 2, 2, 1, 2, 3]
def baseStart_1841846 : Nat := 118140960795 + 1841846 * 2 ^ 59
def prefixEnd_1841846 : Nat := 4983230072969 + 3 ^ 40 * 1841846 * 2
def baseEnd_1841846 : Nat := 945752289561106002754511

theorem tailTrace_1841846 : CollatzResearch.WordTrace tailWord_1841846 prefixEnd_1841846 945752289561106002754511 := by
  unfold tailWord_1841846
  simp only [CollatzResearch.WordTrace]
  refine ⟨4198602655332123693645587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44785094990209319398886261 4198602655332123693645587)
  ·
    refine ⟨6297903982998185540468381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4198602655332123693645587 6297903982998185540468381)
    ·
      refine ⟨2361713993624319577675643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6297903982998185540468381 2361713993624319577675643)
      ·
        refine ⟨3542570990436479366513465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2361713993624319577675643 3542570990436479366513465)
        ·
          refine ⟨2656928242827359524885099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3542570990436479366513465 2656928242827359524885099)
          ·
            refine ⟨3985392364241039287327649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2656928242827359524885099 3985392364241039287327649)
            ·
              refine ⟨2989044273180779465495737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3985392364241039287327649 2989044273180779465495737)
              ·
                refine ⟨2241783204885584599121803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2989044273180779465495737 2241783204885584599121803)
                ·
                  refine ⟨3362674807328376898682705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2241783204885584599121803 3362674807328376898682705)
                  ·
                    refine ⟨2522006105496282674012029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3362674807328376898682705 2522006105496282674012029)
                    ·
                      refine ⟨945752289561106002754511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2522006105496282674012029 945752289561106002754511)
                      ·
                        rfl

theorem cell23_1841846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_1841846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1841846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1841846 prefixEnd_1841846 := by exact prefixLift 1841846
  have htrace : WordTrace (prefixWord ++ tailWord_1841846) baseStart_1841846 baseEnd_1841846 := by
    simpa [prefixWord, tailWord_1841846, baseEnd_1841846] using wordTrace_append hprefix tailTrace_1841846
  have hstable : (prefixWord ++ tailWord_1841846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841846).length < 2 ^ (prefixWord ++ tailWord_1841846).sum := by decide
  have hdescent : baseEnd_1841846 < baseStart_1841846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841882 : List Nat := [3, 1, 1, 2, 2, 2, 1, 3, 4, 2, 2]
def baseStart_1841882 : Nat := 118140960795 + 1841882 * 2 ^ 59
def prefixEnd_1841882 : Nat := 4983230072969 + 3 ^ 40 * 1841882 * 2
def baseEnd_1841882 : Nat := 945770774864667861904345

theorem tailTrace_1841882 : CollatzResearch.WordTrace tailWord_1841882 prefixEnd_1841882 945770774864667861904345 := by
  unfold tailWord_1841882
  simp only [CollatzResearch.WordTrace]
  refine ⟨16794738878295889311659975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44785970342122371497759933 16794738878295889311659975)
  ·
    refine ⟨25192108317443833967489963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16794738878295889311659975 25192108317443833967489963)
    ·
      refine ⟨37788162476165750951234945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25192108317443833967489963 37788162476165750951234945)
      ·
        refine ⟨28341121857124313213426209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37788162476165750951234945 28341121857124313213426209)
        ·
          refine ⟨21255841392843234910069657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28341121857124313213426209 21255841392843234910069657)
          ·
            refine ⟨15941881044632426182552243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21255841392843234910069657 15941881044632426182552243)
            ·
              refine ⟨23912821566948639273828365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15941881044632426182552243 23912821566948639273828365)
              ·
                refine ⟨8967308087605739727685637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23912821566948639273828365 8967308087605739727685637)
                ·
                  refine ⟨1681370266426076198941057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8967308087605739727685637 1681370266426076198941057)
                  ·
                    refine ⟨1261027699819557149205793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1681370266426076198941057 1261027699819557149205793)
                    ·
                      refine ⟨945770774864667861904345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1261027699819557149205793 945770774864667861904345)
                      ·
                        rfl

theorem cell23_1841882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 4, 2, 2].length) (baseStart_1841882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1841882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1841882 prefixEnd_1841882 := by exact prefixLift 1841882
  have htrace : WordTrace (prefixWord ++ tailWord_1841882) baseStart_1841882 baseEnd_1841882 := by
    simpa [prefixWord, tailWord_1841882, baseEnd_1841882] using wordTrace_append hprefix tailTrace_1841882
  have hstable : (prefixWord ++ tailWord_1841882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841882).length < 2 ^ (prefixWord ++ tailWord_1841882).sum := by decide
  have hdescent : baseEnd_1841882 < baseStart_1841882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841925 : List Nat := [1, 3, 1, 1, 2, 1, 1, 2, 4, 5, 2]
def baseStart_1841925 : Nat := 118140960795 + 1841925 * 2 ^ 59
def prefixEnd_1841925 : Nat := 4983230072969 + 3 ^ 40 * 1841925 * 2
def baseEnd_1841925 : Nat := 945792854532811193666647

theorem tailTrace_1841925 : CollatzResearch.WordTrace tailWord_1841925 prefixEnd_1841925 945792854532811193666647 := by
  unfold tailWord_1841925
  simp only [CollatzResearch.WordTrace]
  refine ⟨67180523852027775590455229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44787015901351850393636819 67180523852027775590455229)
  ·
    refine ⟨25192696444510415846420711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67180523852027775590455229 25192696444510415846420711)
    ·
      refine ⟨37789044666765623769631067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25192696444510415846420711 37789044666765623769631067)
      ·
        refine ⟨56683567000148435654446601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37789044666765623769631067 56683567000148435654446601)
        ·
          refine ⟨42512675250111326740834951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56683567000148435654446601 42512675250111326740834951)
          ·
            refine ⟨63769012875166990111252427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42512675250111326740834951 63769012875166990111252427)
            ·
              refine ⟨95653519312750485166878641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63769012875166990111252427 95653519312750485166878641)
              ·
                refine ⟨71740139484562863875158981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95653519312750485166878641 71740139484562863875158981)
                ·
                  refine ⟨13451276153355536976592309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71740139484562863875158981 13451276153355536976592309)
                  ·
                    refine ⟨1261057139377081591555529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13451276153355536976592309 1261057139377081591555529)
                    ·
                      refine ⟨945792854532811193666647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1261057139377081591555529 945792854532811193666647)
                      ·
                        rfl

theorem cell23_1841925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 5, 2].length) (baseStart_1841925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1841925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1841925 prefixEnd_1841925 := by exact prefixLift 1841925
  have htrace : WordTrace (prefixWord ++ tailWord_1841925) baseStart_1841925 baseEnd_1841925 := by
    simpa [prefixWord, tailWord_1841925, baseEnd_1841925] using wordTrace_append hprefix tailTrace_1841925
  have hstable : (prefixWord ++ tailWord_1841925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841925).length < 2 ^ (prefixWord ++ tailWord_1841925).sum := by decide
  have hdescent : baseEnd_1841925 < baseStart_1841925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841949 : List Nat := [1, 4, 2, 4, 1, 1, 1, 1, 2, 3, 3]
def baseStart_1841949 : Nat := 118140960795 + 1841949 * 2 ^ 59
def prefixEnd_1841949 : Nat := 4983230072969 + 3 ^ 40 * 1841949 * 2
def baseEnd_1841949 : Nat := 945805178068519099766537

theorem tailTrace_1841949 : CollatzResearch.WordTrace tailWord_1841949 prefixEnd_1841949 945805178068519099766537 := by
  unfold tailWord_1841949
  simp only [CollatzResearch.WordTrace]
  refine ⟨67181399203940827689328901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44787599469293885126219267 67181399203940827689328901)
  ·
    refine ⟨12596512350738905191749169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67181399203940827689328901 12596512350738905191749169)
    ·
      refine ⟨9447384263054178893811877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12596512350738905191749169 9447384263054178893811877)
      ·
        refine ⟨1771384549322658542589727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9447384263054178893811877 1771384549322658542589727)
        ·
          refine ⟨2657076823983987813884591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1771384549322658542589727 2657076823983987813884591)
          ·
            refine ⟨3985615235975981720826887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2657076823983987813884591 3985615235975981720826887)
            ·
              refine ⟨5978422853963972581240331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3985615235975981720826887 5978422853963972581240331)
              ·
                refine ⟨8967634280945958871860497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5978422853963972581240331 8967634280945958871860497)
                ·
                  refine ⟨6725725710709469153895373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8967634280945958871860497 6725725710709469153895373)
                  ·
                    refine ⟨2522147141516050932710765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6725725710709469153895373 2522147141516050932710765)
                    ·
                      refine ⟨945805178068519099766537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2522147141516050932710765 945805178068519099766537)
                      ·
                        rfl

theorem cell23_1841949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_1841949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1841949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1841949 prefixEnd_1841949 := by exact prefixLift 1841949
  have htrace : WordTrace (prefixWord ++ tailWord_1841949) baseStart_1841949 baseEnd_1841949 := by
    simpa [prefixWord, tailWord_1841949, baseEnd_1841949] using wordTrace_append hprefix tailTrace_1841949
  have hstable : (prefixWord ++ tailWord_1841949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841949).length < 2 ^ (prefixWord ++ tailWord_1841949).sum := by decide
  have hdescent : baseEnd_1841949 < baseStart_1841949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841968 : List Nat := [2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 6]
def baseStart_1841968 : Nat := 118140960795 + 1841968 * 2 ^ 59
def prefixEnd_1841968 : Nat := 4983230072969 + 3 ^ 40 * 1841968 * 2
def baseEnd_1841968 : Nat := 945814934200954525428949

theorem tailTrace_1841968 : CollatzResearch.WordTrace tailWord_1841968 prefixEnd_1841968 945814934200954525428949 := by
  unfold tailWord_1841968
  simp only [CollatzResearch.WordTrace]
  refine ⟨33591046095435996967135279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44788061460581329289513705 33591046095435996967135279)
  ·
    refine ⟨50386569143153995450702919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33591046095435996967135279 50386569143153995450702919)
    ·
      refine ⟨75579853714730993176054379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50386569143153995450702919 75579853714730993176054379)
      ·
        refine ⟨113369780572096489764081569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75579853714730993176054379 113369780572096489764081569)
        ·
          refine ⟨85027335429072367323061177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113369780572096489764081569 85027335429072367323061177)
          ·
            refine ⟨63770501571804275492295883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85027335429072367323061177 63770501571804275492295883)
            ·
              refine ⟨95655752357706413238443825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63770501571804275492295883 95655752357706413238443825)
              ·
                refine ⟨71741814268279809928832869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95655752357706413238443825 71741814268279809928832869)
                ·
                  refine ⟨13451590175302464361656163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71741814268279809928832869 13451590175302464361656163)
                  ·
                    refine ⟨20177385262953696542484245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13451590175302464361656163 20177385262953696542484245)
                    ·
                      refine ⟨945814934200954525428949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20177385262953696542484245 945814934200954525428949)
                      ·
                        rfl

theorem cell23_1841968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 6].length) (baseStart_1841968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1841968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1841968 prefixEnd_1841968 := by exact prefixLift 1841968
  have htrace : WordTrace (prefixWord ++ tailWord_1841968) baseStart_1841968 baseEnd_1841968 := by
    simpa [prefixWord, tailWord_1841968, baseEnd_1841968] using wordTrace_append hprefix tailTrace_1841968
  have hstable : (prefixWord ++ tailWord_1841968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841968).length < 2 ^ (prefixWord ++ tailWord_1841968).sum := by decide
  have hdescent : baseEnd_1841968 < baseStart_1841968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841975 : List Nat := [1, 1, 3, 1, 2, 1, 5, 1, 1, 4, 3]
def baseStart_1841975 : Nat := 118140960795 + 1841975 * 2 ^ 59
def prefixEnd_1841975 : Nat := 4983230072969 + 3 ^ 40 * 1841975 * 2
def baseEnd_1841975 : Nat := 945818528565535998041417

theorem tailTrace_1841975 : CollatzResearch.WordTrace tailWord_1841975 prefixEnd_1841975 945818528565535998041417 := by
  unfold tailWord_1841975
  simp only [CollatzResearch.WordTrace]
  refine ⟨67182347501846634129775379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44788231667897756086516919 67182347501846634129775379)
  ·
    refine ⟨100773521252769951194663069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67182347501846634129775379 100773521252769951194663069)
    ·
      refine ⟨37790070469788731697998651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100773521252769951194663069 37790070469788731697998651)
      ·
        refine ⟨56685105704683097546997977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37790070469788731697998651 56685105704683097546997977)
        ·
          refine ⟨42513829278512323160248483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56685105704683097546997977 42513829278512323160248483)
          ·
            refine ⟨63770743917768484740372725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42513829278512323160248483 63770743917768484740372725)
            ·
              refine ⟨5978507242290795444409943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63770743917768484740372725 5978507242290795444409943)
              ·
                refine ⟨8967760863436193166614915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5978507242290795444409943 8967760863436193166614915)
                ·
                  refine ⟨13451641295154289749922373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8967760863436193166614915 13451641295154289749922373)
                  ·
                    refine ⟨2522182742841429328110445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13451641295154289749922373 2522182742841429328110445)
                    ·
                      refine ⟨945818528565535998041417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2522182742841429328110445 945818528565535998041417)
                      ·
                        rfl

theorem cell23_1841975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 4, 3].length) (baseStart_1841975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1841975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1841975 prefixEnd_1841975 := by exact prefixLift 1841975
  have htrace : WordTrace (prefixWord ++ tailWord_1841975) baseStart_1841975 baseEnd_1841975 := by
    simpa [prefixWord, tailWord_1841975, baseEnd_1841975] using wordTrace_append hprefix tailTrace_1841975
  have hstable : (prefixWord ++ tailWord_1841975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841975).length < 2 ^ (prefixWord ++ tailWord_1841975).sum := by decide
  have hdescent : baseEnd_1841975 < baseStart_1841975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842032 : List Nat := [2, 1, 1, 1, 4, 1, 4, 1, 1, 5, 2]
def baseStart_1842032 : Nat := 118140960795 + 1842032 * 2 ^ 59
def prefixEnd_1842032 : Nat := 4983230072969 + 3 ^ 40 * 1842032 * 2
def baseEnd_1842032 : Nat := 945847796962842275028655

theorem tailTrace_1842032 : CollatzResearch.WordTrace tailWord_1842032 prefixEnd_1842032 945847796962842275028655 := by
  unfold tailWord_1842032
  simp only [CollatzResearch.WordTrace]
  refine ⟨33592213231320066432300175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44789617641760088576400233 33592213231320066432300175)
  ·
    refine ⟨50388319846980099648450263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33592213231320066432300175 50388319846980099648450263)
    ·
      refine ⟨75582479770470149472675395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50388319846980099648450263 75582479770470149472675395)
      ·
        refine ⟨113373719655705224209013093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75582479770470149472675395 113373719655705224209013093)
        ·
          refine ⟨21257572435444729539189955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113373719655705224209013093 21257572435444729539189955)
          ·
            refine ⟨31886358653167094308784933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21257572435444729539189955 31886358653167094308784933)
            ·
              refine ⟨5978692247468830182897175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31886358653167094308784933 5978692247468830182897175)
              ·
                refine ⟨8968038371203245274345763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5978692247468830182897175 8968038371203245274345763)
                ·
                  refine ⟨13452057556804867911518645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8968038371203245274345763 13452057556804867911518645)
                  ·
                    refine ⟨1261130395950456366704873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13452057556804867911518645 1261130395950456366704873)
                    ·
                      refine ⟨945847796962842275028655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1261130395950456366704873 945847796962842275028655)
                      ·
                        rfl

theorem cell23_1842032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 1, 5, 2].length) (baseStart_1842032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1842032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1842032 prefixEnd_1842032 := by exact prefixLift 1842032
  have htrace : WordTrace (prefixWord ++ tailWord_1842032) baseStart_1842032 baseEnd_1842032 := by
    simpa [prefixWord, tailWord_1842032, baseEnd_1842032] using wordTrace_append hprefix tailTrace_1842032
  have hstable : (prefixWord ++ tailWord_1842032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842032).length < 2 ^ (prefixWord ++ tailWord_1842032).sum := by decide
  have hdescent : baseEnd_1842032 < baseStart_1842032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842050 : List Nat := [3, 4, 2, 2, 2, 1, 1, 1, 3, 4]
def baseStart_1842050 : Nat := 118140960795 + 1842050 * 2 ^ 59
def prefixEnd_1842050 : Nat := 4983230072969 + 3 ^ 40 * 1842050 * 2
def baseEnd_1842050 : Nat := 315285679871541068201191

theorem tailTrace_1842050 : CollatzResearch.WordTrace tailWord_1842050 prefixEnd_1842050 315285679871541068201191 := by
  unfold tailWord_1842050
  simp only [CollatzResearch.WordTrace]
  refine ⟨16796270744143730484688901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44790055317716614625837069 16796270744143730484688901)
  ·
    refine ⟨3149300764526949465879169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16796270744143730484688901 3149300764526949465879169)
    ·
      refine ⟨2361975573395212099409377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3149300764526949465879169 2361975573395212099409377)
      ·
        refine ⟨1771481680046409074557033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2361975573395212099409377 1771481680046409074557033)
        ·
          refine ⟨1328611260034806805917775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1771481680046409074557033 1328611260034806805917775)
          ·
            refine ⟨1992916890052210208876663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1328611260034806805917775 1992916890052210208876663)
            ·
              refine ⟨2989375335078315313314995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1992916890052210208876663 2989375335078315313314995)
              ·
                refine ⟨4484063002617472969972493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2989375335078315313314995 4484063002617472969972493)
                ·
                  refine ⟨1681523625981552363739685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4484063002617472969972493 1681523625981552363739685)
                  ·
                    refine ⟨315285679871541068201191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1681523625981552363739685 315285679871541068201191)
                    ·
                      rfl

theorem cell23_1842050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_1842050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1842050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1842050 prefixEnd_1842050 := by exact prefixLift 1842050
  have htrace : WordTrace (prefixWord ++ tailWord_1842050) baseStart_1842050 baseEnd_1842050 := by
    simpa [prefixWord, tailWord_1842050, baseEnd_1842050] using wordTrace_append hprefix tailTrace_1842050
  have hstable : (prefixWord ++ tailWord_1842050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842050).length < 2 ^ (prefixWord ++ tailWord_1842050).sum := by decide
  have hdescent : baseEnd_1842050 < baseStart_1842050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842056 : List Nat := [2, 1, 3, 3, 2, 3, 1, 1, 3, 1, 3]
def baseStart_1842056 : Nat := 118140960795 + 1842056 * 2 ^ 59
def prefixEnd_1842056 : Nat := 4983230072969 + 3 ^ 40 * 1842056 * 2
def baseEnd_1842056 : Nat := 945860120498550181128545

theorem tailTrace_1842056 : CollatzResearch.WordTrace tailWord_1842056 prefixEnd_1842056 945860120498550181128545 := by
  unfold tailWord_1842056
  simp only [CollatzResearch.WordTrace]
  refine ⟨33592650907276592481737011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44790201209702123308982681 33592650907276592481737011)
  ·
    refine ⟨50388976360914888722605517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33592650907276592481737011 50388976360914888722605517)
    ·
      refine ⟨18895866135343083270977069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50388976360914888722605517 18895866135343083270977069)
      ·
        refine ⟨7085949800753656226616401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18895866135343083270977069 7085949800753656226616401)
        ·
          refine ⟨5314462350565242169962301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7085949800753656226616401 5314462350565242169962301)
          ·
            refine ⟨1992923381461965813735863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5314462350565242169962301 1992923381461965813735863)
            ·
              refine ⟨2989385072192948720603795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1992923381461965813735863 2989385072192948720603795)
              ·
                refine ⟨4484077608289423080905693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2989385072192948720603795 4484077608289423080905693)
                ·
                  refine ⟨1681529103108533655339635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4484077608289423080905693 1681529103108533655339635)
                  ·
                    refine ⟨2522293654662800483009453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1681529103108533655339635 2522293654662800483009453)
                    ·
                      refine ⟨945860120498550181128545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2522293654662800483009453 945860120498550181128545)
                      ·
                        rfl

theorem cell23_1842056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_1842056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1842056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1842056 prefixEnd_1842056 := by exact prefixLift 1842056
  have htrace : WordTrace (prefixWord ++ tailWord_1842056) baseStart_1842056 baseEnd_1842056 := by
    simpa [prefixWord, tailWord_1842056, baseEnd_1842056] using wordTrace_append hprefix tailTrace_1842056
  have hstable : (prefixWord ++ tailWord_1842056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842056).length < 2 ^ (prefixWord ++ tailWord_1842056).sum := by decide
  have hdescent : baseEnd_1842056 < baseStart_1842056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842065 : List Nat := [1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 3]
def baseStart_1842065 : Nat := 118140960795 + 1842065 * 2 ^ 59
def prefixEnd_1842065 : Nat := 4983230072969 + 3 ^ 40 * 1842065 * 2
def baseEnd_1842065 : Nat := 945864741824440645916003

theorem tailTrace_1842065 : CollatzResearch.WordTrace tailWord_1842065 prefixEnd_1842065 945864741824440645916003 := by
  unfold tailWord_1842065
  simp only [CollatzResearch.WordTrace]
  refine ⟨67185630071520579500551649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44790420047680386333701099 67185630071520579500551649)
  ·
    refine ⟨50389222553640434625413737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67185630071520579500551649 50389222553640434625413737)
    ·
      refine ⟨37791916915230325969060303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50389222553640434625413737 37791916915230325969060303)
      ·
        refine ⟨56687875372845488953590455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37791916915230325969060303 56687875372845488953590455)
        ·
          refine ⟨85031813059268233430385683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56687875372845488953590455 85031813059268233430385683)
          ·
            refine ⟨127547719588902350145578525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85031813059268233430385683 127547719588902350145578525)
            ·
              refine ⟨47830394845838381304591947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127547719588902350145578525 47830394845838381304591947)
              ·
                refine ⟨71745592268757571956887921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47830394845838381304591947 71745592268757571956887921)
                ·
                  refine ⟨53809194201568178967665941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71745592268757571956887921 53809194201568178967665941)
                  ·
                    refine ⟨2522305978198508389109341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 53809194201568178967665941 2522305978198508389109341)
                    ·
                      refine ⟨945864741824440645916003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2522305978198508389109341 945864741824440645916003)
                      ·
                        rfl

theorem cell23_1842065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 3].length) (baseStart_1842065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1842065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1842065 prefixEnd_1842065 := by exact prefixLift 1842065
  have htrace : WordTrace (prefixWord ++ tailWord_1842065) baseStart_1842065 baseEnd_1842065 := by
    simpa [prefixWord, tailWord_1842065, baseEnd_1842065] using wordTrace_append hprefix tailTrace_1842065
  have hstable : (prefixWord ++ tailWord_1842065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842065).length < 2 ^ (prefixWord ++ tailWord_1842065).sum := by decide
  have hdescent : baseEnd_1842065 < baseStart_1842065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842076 : List Nat := [2, 2, 3, 3, 2, 2, 1, 2, 1, 5]
def baseStart_1842076 : Nat := 118140960795 + 1842076 * 2 ^ 59
def prefixEnd_1842076 : Nat := 4983230072969 + 3 ^ 40 * 1842076 * 2
def baseEnd_1842076 : Nat := 315290130037213367626151

theorem tailTrace_1842076 : CollatzResearch.WordTrace tailWord_1842076 prefixEnd_1842076 315290130037213367626151 := by
  unfold tailWord_1842076
  simp only [CollatzResearch.WordTrace]
  refine ⟨33593015637240364189601041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44790687516320485586134721 33593015637240364189601041)
  ·
    refine ⟨25194761727930273142200781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33593015637240364189601041 25194761727930273142200781)
    ·
      refine ⟨9448035647973852428325293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25194761727930273142200781 9448035647973852428325293)
      ·
        refine ⟨3543013367990194660621985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9448035647973852428325293 3543013367990194660621985)
        ·
          refine ⟨2657260025992645995466489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3543013367990194660621985 2657260025992645995466489)
          ·
            refine ⟨1992945019494484496599867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2657260025992645995466489 1992945019494484496599867)
            ·
              refine ⟨2989417529241726744899801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1992945019494484496599867 2989417529241726744899801)
              ·
                refine ⟨2242063146931295058674851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2989417529241726744899801 2242063146931295058674851)
                ·
                  refine ⟨3363094720396942588012277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2242063146931295058674851 3363094720396942588012277)
                  ·
                    refine ⟨315290130037213367626151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3363094720396942588012277 315290130037213367626151)
                    ·
                      rfl

theorem cell23_1842076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_1842076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1842076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1842076 prefixEnd_1842076 := by exact prefixLift 1842076
  have htrace : WordTrace (prefixWord ++ tailWord_1842076) baseStart_1842076 baseEnd_1842076 := by
    simpa [prefixWord, tailWord_1842076, baseEnd_1842076] using wordTrace_append hprefix tailTrace_1842076
  have hstable : (prefixWord ++ tailWord_1842076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842076).length < 2 ^ (prefixWord ++ tailWord_1842076).sum := by decide
  have hdescent : baseEnd_1842076 < baseStart_1842076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842079 : List Nat := [1, 1, 2, 5, 2, 1, 3, 2, 1, 1, 4]
def baseStart_1842079 : Nat := 118140960795 + 1842079 * 2 ^ 59
def prefixEnd_1842079 : Nat := 4983230072969 + 3 ^ 40 * 1842079 * 2
def baseEnd_1842079 : Nat := 945871930553603591140939

theorem tailTrace_1842079 : CollatzResearch.WordTrace tailWord_1842079 prefixEnd_1842079 945871930553603591140939 := by
  unfold tailWord_1842079
  simp only [CollatzResearch.WordTrace]
  refine ⟨67186140693469859891561291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44790760462313239927707527 67186140693469859891561291)
  ·
    refine ⟨100779211040204789837341937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67186140693469859891561291 100779211040204789837341937)
    ·
      refine ⟨75584408280153592378006453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100779211040204789837341937 75584408280153592378006453)
      ·
        refine ⟨7086038276264399285438105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75584408280153592378006453 7086038276264399285438105)
        ·
          refine ⟨5314528707198299464078579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7086038276264399285438105 5314528707198299464078579)
          ·
            refine ⟨7971793060797449196117869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5314528707198299464078579 7971793060797449196117869)
            ·
              refine ⟨2989422397799043448544201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7971793060797449196117869 2989422397799043448544201)
              ·
                refine ⟨2242066798349282586408151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2989422397799043448544201 2242066798349282586408151)
                ·
                  refine ⟨3363100197523923879612227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2242066798349282586408151 3363100197523923879612227)
                  ·
                    refine ⟨5044650296285885819418341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3363100197523923879612227 5044650296285885819418341)
                    ·
                      refine ⟨945871930553603591140939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5044650296285885819418341 945871930553603591140939)
                      ·
                        rfl

theorem cell23_1842079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_1842079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1842079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1842079 prefixEnd_1842079 := by exact prefixLift 1842079
  have htrace : WordTrace (prefixWord ++ tailWord_1842079) baseStart_1842079 baseEnd_1842079 := by
    simpa [prefixWord, tailWord_1842079, baseEnd_1842079] using wordTrace_append hprefix tailTrace_1842079
  have hstable : (prefixWord ++ tailWord_1842079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842079).length < 2 ^ (prefixWord ++ tailWord_1842079).sum := by decide
  have hdescent : baseEnd_1842079 < baseStart_1842079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842093 : List Nat := [1, 5, 2, 3, 1, 1, 3, 1, 1, 5]
def baseStart_1842093 : Nat := 118140960795 + 1842093 * 2 ^ 59
def prefixEnd_1842093 : Nat := 4983230072969 + 3 ^ 40 * 1842093 * 2
def baseEnd_1842093 : Nat := 315293039760922178788625

theorem tailTrace_1842093 : CollatzResearch.WordTrace tailWord_1842093 prefixEnd_1842093 315293039760922178788625 := by
  unfold tailWord_1842093
  simp only [CollatzResearch.WordTrace]
  refine ⟨67186651315419140282570933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44791100876946093521713955 67186651315419140282570933)
  ·
    refine ⟨6298748560820544401491025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67186651315419140282570933 6298748560820544401491025)
    ·
      refine ⟨4724061420615408301118269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6298748560820544401491025 4724061420615408301118269)
      ·
        refine ⟨1771523032730778112919351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4724061420615408301118269 1771523032730778112919351)
        ·
          refine ⟨2657284549096167169379027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1771523032730778112919351 2657284549096167169379027)
          ·
            refine ⟨3985926823644250754068541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2657284549096167169379027 3985926823644250754068541)
            ·
              refine ⟨1494722558866594032775703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3985926823644250754068541 1494722558866594032775703)
              ·
                refine ⟨2242083838299891049163555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1494722558866594032775703 2242083838299891049163555)
                ·
                  refine ⟨3363125757449836573745333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2242083838299891049163555 3363125757449836573745333)
                  ·
                    refine ⟨315293039760922178788625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3363125757449836573745333 315293039760922178788625)
                    ·
                      rfl

theorem cell23_1842093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_1842093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1842093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1842093 prefixEnd_1842093 := by exact prefixLift 1842093
  have htrace : WordTrace (prefixWord ++ tailWord_1842093) baseStart_1842093 baseEnd_1842093 := by
    simpa [prefixWord, tailWord_1842093, baseEnd_1842093] using wordTrace_append hprefix tailTrace_1842093
  have hstable : (prefixWord ++ tailWord_1842093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842093).length < 2 ^ (prefixWord ++ tailWord_1842093).sum := by decide
  have hdescent : baseEnd_1842093 < baseStart_1842093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842129 : List Nat := [1, 2, 2, 1, 2, 1, 3, 5, 2, 1, 3]
def baseStart_1842129 : Nat := 118140960795 + 1842129 * 2 ^ 59
def prefixEnd_1842129 : Nat := 4983230072969 + 3 ^ 40 * 1842129 * 2
def baseEnd_1842129 : Nat := 945897604586328395515709

theorem tailTrace_1842129 : CollatzResearch.WordTrace tailWord_1842129 prefixEnd_1842129 945897604586328395515709 := by
  unfold tailWord_1842129
  simp only [CollatzResearch.WordTrace]
  refine ⟨67187964343288718430881441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44791976228859145620587627 67187964343288718430881441)
  ·
    refine ⟨50390973257466538823161081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67187964343288718430881441 50390973257466538823161081)
    ·
      refine ⟨37793229943099904117370811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50390973257466538823161081 37793229943099904117370811)
      ·
        refine ⟨56689844914649856176056217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37793229943099904117370811 56689844914649856176056217)
        ·
          refine ⟨42517383685987392132042163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56689844914649856176056217 42517383685987392132042163)
          ·
            refine ⟨63776075528981088198063245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42517383685987392132042163 63776075528981088198063245)
            ·
              refine ⟨23916028323367908074273717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63776075528981088198063245 23916028323367908074273717)
              ·
                refine ⟨2242127655315741381963161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23916028323367908074273717 2242127655315741381963161)
                ·
                  refine ⟨1681595741486806036472371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2242127655315741381963161 1681595741486806036472371)
                  ·
                    refine ⟨2522393612230209054708557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1681595741486806036472371 2522393612230209054708557)
                    ·
                      refine ⟨945897604586328395515709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2522393612230209054708557 945897604586328395515709)
                      ·
                        rfl

theorem cell23_1842129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 5, 2, 1, 3].length) (baseStart_1842129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1842129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1842129 prefixEnd_1842129 := by exact prefixLift 1842129
  have htrace : WordTrace (prefixWord ++ tailWord_1842129) baseStart_1842129 baseEnd_1842129 := by
    simpa [prefixWord, tailWord_1842129, baseEnd_1842129] using wordTrace_append hprefix tailTrace_1842129
  have hstable : (prefixWord ++ tailWord_1842129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842129).length < 2 ^ (prefixWord ++ tailWord_1842129).sum := by decide
  have hdescent : baseEnd_1842129 < baseStart_1842129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842145 : List Nat := [1, 2, 3, 1, 2, 1, 1, 1, 3, 8]
def baseStart_1842145 : Nat := 118140960795 + 1842145 * 2 ^ 59
def prefixEnd_1842145 : Nat := 4983230072969 + 3 ^ 40 * 1842145 * 2
def baseEnd_1842145 : Nat := 315301940092266777638545

theorem tailTrace_1842145 : CollatzResearch.WordTrace tailWord_1842145 prefixEnd_1842145 315301940092266777638545 := by
  unfold tailWord_1842145
  simp only [CollatzResearch.WordTrace]
  refine ⟨67188547911230753163463889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44792365274153835442309259 67188547911230753163463889)
  ·
    refine ⟨50391410933423064872597917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67188547911230753163463889 50391410933423064872597917)
    ·
      refine ⟨18896779100033649327224219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50391410933423064872597917 18896779100033649327224219)
      ·
        refine ⟨28345168650050473990836329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18896779100033649327224219 28345168650050473990836329)
        ·
          refine ⟨21258876487537855493127247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28345168650050473990836329 21258876487537855493127247)
          ·
            refine ⟨31888314731306783239690871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21258876487537855493127247 31888314731306783239690871)
            ·
              refine ⟨47832472096960174859536307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31888314731306783239690871 47832472096960174859536307)
              ·
                refine ⟨71748708145440262289304461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47832472096960174859536307 71748708145440262289304461)
                ·
                  refine ⟨26905765554540098358489173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71748708145440262289304461 26905765554540098358489173)
                  ·
                    refine ⟨315301940092266777638545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 26905765554540098358489173 315301940092266777638545)
                    ·
                      rfl

theorem cell23_1842145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 8].length) (baseStart_1842145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1842145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1842145 prefixEnd_1842145 := by exact prefixLift 1842145
  have htrace : WordTrace (prefixWord ++ tailWord_1842145) baseStart_1842145 baseEnd_1842145 := by
    simpa [prefixWord, tailWord_1842145, baseEnd_1842145] using wordTrace_append hprefix tailTrace_1842145
  have hstable : (prefixWord ++ tailWord_1842145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842145).length < 2 ^ (prefixWord ++ tailWord_1842145).sum := by decide
  have hdescent : baseEnd_1842145 < baseStart_1842145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842146 : List Nat := [3, 3, 3, 1, 1, 1, 2, 2, 1, 3, 3]
def baseStart_1842146 : Nat := 118140960795 + 1842146 * 2 ^ 59
def prefixEnd_1842146 : Nat := 4983230072969 + 3 ^ 40 * 1842146 * 2
def baseEnd_1842146 : Nat := 945906333757454829003131

theorem tailTrace_1842146 : CollatzResearch.WordTrace tailWord_1842146 prefixEnd_1842146 945906333757454829003131 := by
  unfold tailWord_1842146
  simp only [CollatzResearch.WordTrace]
  refine ⟨16797146096056782583562573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44792389589484753556166861 16797146096056782583562573)
  ·
    refine ⟨6298929786021293468835965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16797146096056782583562573 6298929786021293468835965)
    ·
      refine ⟨2362098669757985050813487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6298929786021293468835965 2362098669757985050813487)
      ·
        refine ⟨3543148004636977576220231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2362098669757985050813487 3543148004636977576220231)
        ·
          refine ⟨5314722006955466364330347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3543148004636977576220231 5314722006955466364330347)
          ·
            refine ⟨7972083010433199546495521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5314722006955466364330347 7972083010433199546495521)
            ·
              refine ⟨5979062257824899659871641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7972083010433199546495521 5979062257824899659871641)
              ·
                refine ⟨4484296693368674744903731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5979062257824899659871641 4484296693368674744903731)
                ·
                  refine ⟨6726445040053012117355597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4484296693368674744903731 6726445040053012117355597)
                  ·
                    refine ⟨2522416890019879544008349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6726445040053012117355597 2522416890019879544008349)
                    ·
                      refine ⟨945906333757454829003131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2522416890019879544008349 945906333757454829003131)
                      ·
                        rfl

theorem cell23_1842146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_1842146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1842146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1842146 prefixEnd_1842146 := by exact prefixLift 1842146
  have htrace : WordTrace (prefixWord ++ tailWord_1842146) baseStart_1842146 baseEnd_1842146 := by
    simpa [prefixWord, tailWord_1842146, baseEnd_1842146] using wordTrace_append hprefix tailTrace_1842146
  have hstable : (prefixWord ++ tailWord_1842146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842146).length < 2 ^ (prefixWord ++ tailWord_1842146).sum := by decide
  have hdescent : baseEnd_1842146 < baseStart_1842146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842164 : List Nat := [2, 6, 2, 1, 1, 1, 2, 1, 3, 2, 2]
def baseStart_1842164 : Nat := 118140960795 + 1842164 * 2 ^ 59
def prefixEnd_1842164 : Nat := 4983230072969 + 3 ^ 40 * 1842164 * 2
def baseEnd_1842164 : Nat := 945915576409235758578049

theorem tailTrace_1842164 : CollatzResearch.WordTrace tailWord_1842164 prefixEnd_1842164 945915576409235758578049 := by
  unfold tailWord_1842164
  simp only [CollatzResearch.WordTrace]
  refine ⟨33594620449080959704202773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44792827265441279605603697 33594620449080959704202773)
  ·
    refine ⟨1574747833550669986134505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 33594620449080959704202773 1574747833550669986134505)
    ·
      refine ⟨1181060875163002489600879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1574747833550669986134505 1181060875163002489600879)
      ·
        refine ⟨1771591312744503734401319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1181060875163002489600879 1771591312744503734401319)
        ·
          refine ⟨2657386969116755601601979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1771591312744503734401319 2657386969116755601601979)
          ·
            refine ⟨3986080453675133402402969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2657386969116755601601979 3986080453675133402402969)
            ·
              refine ⟨2989560340256350051802227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3986080453675133402402969 2989560340256350051802227)
              ·
                refine ⟨4484340510384525077703341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2989560340256350051802227 4484340510384525077703341)
                ·
                  refine ⟨1681627691394196904138753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4484340510384525077703341 1681627691394196904138753)
                  ·
                    refine ⟨1261220768545647678104065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1681627691394196904138753 1261220768545647678104065)
                    ·
                      refine ⟨945915576409235758578049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1261220768545647678104065 945915576409235758578049)
                      ·
                        rfl

theorem cell23_1842164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_1842164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1842164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1842164 prefixEnd_1842164 := by exact prefixLift 1842164
  have htrace : WordTrace (prefixWord ++ tailWord_1842164) baseStart_1842164 baseEnd_1842164 := by
    simpa [prefixWord, tailWord_1842164, baseEnd_1842164] using wordTrace_append hprefix tailTrace_1842164
  have hstable : (prefixWord ++ tailWord_1842164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842164).length < 2 ^ (prefixWord ++ tailWord_1842164).sum := by decide
  have hdescent : baseEnd_1842164 < baseStart_1842164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842185 : List Nat := [1, 2, 1, 1, 3, 1, 1, 2, 1, 1, 9]
def baseStart_1842185 : Nat := 118140960795 + 1842185 * 2 ^ 59
def prefixEnd_1842185 : Nat := 4983230072969 + 3 ^ 40 * 1842185 * 2
def baseEnd_1842185 : Nat := 945926359502980176415451

theorem tailTrace_1842185 : CollatzResearch.WordTrace tailWord_1842185 prefixEnd_1842185 945926359502980176415451 := by
  unfold tailWord_1842185
  simp only [CollatzResearch.WordTrace]
  refine ⟨67190006831085839994920009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44793337887390559996613339 67190006831085839994920009)
  ·
    refine ⟨50392505123314379996190007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67190006831085839994920009 50392505123314379996190007)
    ·
      refine ⟨75588757684971569994285011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50392505123314379996190007 75588757684971569994285011)
      ·
        refine ⟨113383136527457354991427517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75588757684971569994285011 113383136527457354991427517)
        ·
          refine ⟨42518676197796508121785319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113383136527457354991427517 42518676197796508121785319)
          ·
            refine ⟨63778014296694762182677979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42518676197796508121785319 63778014296694762182677979)
            ·
              refine ⟨95667021445042143274016969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63778014296694762182677979 95667021445042143274016969)
              ·
                refine ⟨71750266083781607455512727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95667021445042143274016969 71750266083781607455512727)
                ·
                  refine ⟨107625399125672411183269091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71750266083781607455512727 107625399125672411183269091)
                  ·
                    refine ⟨161438098688508616774903637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 107625399125672411183269091 161438098688508616774903637)
                    ·
                      refine ⟨945926359502980176415451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 161438098688508616774903637 945926359502980176415451)
                      ·
                        rfl

theorem cell23_1842185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 1, 9].length) (baseStart_1842185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1842185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1842185 prefixEnd_1842185 := by exact prefixLift 1842185
  have htrace : WordTrace (prefixWord ++ tailWord_1842185) baseStart_1842185 baseEnd_1842185 := by
    simpa [prefixWord, tailWord_1842185, baseEnd_1842185] using wordTrace_append hprefix tailTrace_1842185
  have hstable : (prefixWord ++ tailWord_1842185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842185).length < 2 ^ (prefixWord ++ tailWord_1842185).sum := by decide
  have hdescent : baseEnd_1842185 < baseStart_1842185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842186 : List Nat := [3, 1, 2, 2, 3, 1, 3, 1, 1, 4, 2]
def baseStart_1842186 : Nat := 118140960795 + 1842186 * 2 ^ 59
def prefixEnd_1842186 : Nat := 4983230072969 + 3 ^ 40 * 1842186 * 2
def baseEnd_1842186 : Nat := 945926872983634672502947

theorem tailTrace_1842186 : CollatzResearch.WordTrace tailWord_1842186 prefixEnd_1842186 945926872983634672502947 := by
  unfold tailWord_1842186
  simp only [CollatzResearch.WordTrace]
  refine ⟨16797510826020554291426603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44793362202721478110470941 16797510826020554291426603)
  ·
    refine ⟨25196266239030831437139905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16797510826020554291426603 25196266239030831437139905)
    ·
      refine ⟨18897199679273123577854929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25196266239030831437139905 18897199679273123577854929)
      ·
        refine ⟨14172899759454842683391197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18897199679273123577854929 14172899759454842683391197)
        ·
          refine ⟨5314837409795566006271699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14172899759454842683391197 5314837409795566006271699)
          ·
            refine ⟨7972256114693349009407549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5314837409795566006271699 7972256114693349009407549)
            ·
              refine ⟨2989596043010005878527831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7972256114693349009407549 2989596043010005878527831)
              ·
                refine ⟨4484394064515008817791747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2989596043010005878527831 4484394064515008817791747)
                ·
                  refine ⟨6726591096772513226687621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4484394064515008817791747 6726591096772513226687621)
                  ·
                    refine ⟨1261235830644846230003929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6726591096772513226687621 1261235830644846230003929)
                    ·
                      refine ⟨945926872983634672502947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1261235830644846230003929 945926872983634672502947)
                      ·
                        rfl

theorem cell23_1842186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 1, 1, 4, 2].length) (baseStart_1842186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1842186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1842186 prefixEnd_1842186 := by exact prefixLift 1842186
  have htrace : WordTrace (prefixWord ++ tailWord_1842186) baseStart_1842186 baseEnd_1842186 := by
    simpa [prefixWord, tailWord_1842186, baseEnd_1842186] using wordTrace_append hprefix tailTrace_1842186
  have hstable : (prefixWord ++ tailWord_1842186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842186).length < 2 ^ (prefixWord ++ tailWord_1842186).sum := by decide
  have hdescent : baseEnd_1842186 < baseStart_1842186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842226 : List Nat := [3, 2, 1, 1, 2, 2, 5, 2, 5]
def baseStart_1842226 : Nat := 118140960795 + 1842226 * 2 ^ 59
def prefixEnd_1842226 : Nat := 4983230072969 + 3 ^ 40 * 1842226 * 2
def baseEnd_1842226 : Nat := 105105268023312724000307

theorem tailTrace_1842226 : CollatzResearch.WordTrace tailWord_1842226 prefixEnd_1842226 105105268023312724000307 := by
  unfold tailWord_1842226
  simp only [CollatzResearch.WordTrace]
  refine ⟨16797875555984325999290633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44794334815958202664775021 16797875555984325999290633)
  ·
    refine ⟨12598406666988244499467975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16797875555984325999290633 12598406666988244499467975)
    ·
      refine ⟨18897610000482366749201963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12598406666988244499467975 18897610000482366749201963)
      ·
        refine ⟨28346415000723550123802945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18897610000482366749201963 28346415000723550123802945)
        ·
          refine ⟨21259811250542662592852209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28346415000723550123802945 21259811250542662592852209)
          ·
            refine ⟨15944858437906996944639157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21259811250542662592852209 15944858437906996944639157)
            ·
              refine ⟨1494830478553780963559921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15944858437906996944639157 1494830478553780963559921)
              ·
                refine ⟨1121122858915335722669941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1494830478553780963559921 1121122858915335722669941)
                ·
                  refine ⟨105105268023312724000307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1121122858915335722669941 105105268023312724000307)
                  ·
                    rfl

theorem cell23_1842226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 2, 5].length) (baseStart_1842226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1842226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1842226 prefixEnd_1842226 := by exact prefixLift 1842226
  have htrace : WordTrace (prefixWord ++ tailWord_1842226) baseStart_1842226 baseEnd_1842226 := by
    simpa [prefixWord, tailWord_1842226, baseEnd_1842226] using wordTrace_append hprefix tailTrace_1842226
  have hstable : (prefixWord ++ tailWord_1842226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842226).length < 2 ^ (prefixWord ++ tailWord_1842226).sum := by decide
  have hdescent : baseEnd_1842226 < baseStart_1842226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842229 : List Nat := [1, 3, 3, 1, 1, 1, 1, 3, 2, 5, 2]
def baseStart_1842229 : Nat := 118140960795 + 1842229 * 2 ^ 59
def prefixEnd_1842229 : Nat := 4983230072969 + 3 ^ 40 * 1842229 * 2
def baseEnd_1842229 : Nat := 945948952651778004265249

theorem tailTrace_1842229 : CollatzResearch.WordTrace tailWord_1842229 prefixEnd_1842229 945948952651778004265249 := by
  unfold tailWord_1842229
  simp only [CollatzResearch.WordTrace]
  refine ⟨67191611642926435509521741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44794407761950957006347827 67191611642926435509521741)
  ·
    refine ⟨25196854366097413316070653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67191611642926435509521741 25196854366097413316070653)
    ·
      refine ⟨9448820387286529993526495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25196854366097413316070653 9448820387286529993526495)
      ·
        refine ⟨14173230580929794990289743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9448820387286529993526495 14173230580929794990289743)
        ·
          refine ⟨21259845871394692485434615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14173230580929794990289743 21259845871394692485434615)
          ·
            refine ⟨31889768807092038728151923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21259845871394692485434615 31889768807092038728151923)
            ·
              refine ⟨47834653210638058092227885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31889768807092038728151923 47834653210638058092227885)
              ·
                refine ⟨17937994953989271784585457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47834653210638058092227885 17937994953989271784585457)
                ·
                  refine ⟨13453496215491953838439093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17937994953989271784585457 13453496215491953838439093)
                  ·
                    refine ⟨1261265270202370672353665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13453496215491953838439093 1261265270202370672353665)
                    ·
                      refine ⟨945948952651778004265249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1261265270202370672353665 945948952651778004265249)
                      ·
                        rfl

theorem cell23_1842229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 5, 2].length) (baseStart_1842229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1842229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1842229 prefixEnd_1842229 := by exact prefixLift 1842229
  have htrace : WordTrace (prefixWord ++ tailWord_1842229) baseStart_1842229 baseEnd_1842229 := by
    simpa [prefixWord, tailWord_1842229, baseEnd_1842229] using wordTrace_append hprefix tailTrace_1842229
  have hstable : (prefixWord ++ tailWord_1842229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842229).length < 2 ^ (prefixWord ++ tailWord_1842229).sum := by decide
  have hdescent : baseEnd_1842229 < baseStart_1842229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842232 : List Nat := [2, 1, 2, 1, 5, 1, 1, 1, 1, 1, 7]
def baseStart_1842232 : Nat := 118140960795 + 1842232 * 2 ^ 59
def prefixEnd_1842232 : Nat := 4983230072969 + 3 ^ 40 * 1842232 * 2
def baseEnd_1842232 : Nat := 945950493093741492527735

theorem tailTrace_1842232 : CollatzResearch.WordTrace tailWord_1842232 prefixEnd_1842232 945950493093741492527735 := by
  unfold tailWord_1842232
  simp only [CollatzResearch.WordTrace]
  refine ⟨33595860530957783510940475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44794480707943711347920633 33595860530957783510940475)
  ·
    refine ⟨50393790796436675266410713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33595860530957783510940475 50393790796436675266410713)
    ·
      refine ⟨37795343097327506449808035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50393790796436675266410713 37795343097327506449808035)
      ·
        refine ⟨56693014645991259674712053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37795343097327506449808035 56693014645991259674712053)
        ·
          refine ⟨5314970123061680594504255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56693014645991259674712053 5314970123061680594504255)
          ·
            refine ⟨7972455184592520891756383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5314970123061680594504255 7972455184592520891756383)
            ·
              refine ⟨11958682776888781337634575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7972455184592520891756383 11958682776888781337634575)
              ·
                refine ⟨17938024165333172006451863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11958682776888781337634575 17938024165333172006451863)
                ·
                  refine ⟨26907036247999758009677795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17938024165333172006451863 26907036247999758009677795)
                  ·
                    refine ⟨40360554371999637014516693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26907036247999758009677795 40360554371999637014516693)
                    ·
                      refine ⟨945950493093741492527735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 40360554371999637014516693 945950493093741492527735)
                      ·
                        rfl

theorem cell23_1842232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 1, 1, 7].length) (baseStart_1842232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1842232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1842232 prefixEnd_1842232 := by exact prefixLift 1842232
  have htrace : WordTrace (prefixWord ++ tailWord_1842232) baseStart_1842232 baseEnd_1842232 := by
    simpa [prefixWord, tailWord_1842232, baseEnd_1842232] using wordTrace_append hprefix tailTrace_1842232
  have hstable : (prefixWord ++ tailWord_1842232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842232).length < 2 ^ (prefixWord ++ tailWord_1842232).sum := by decide
  have hdescent : baseEnd_1842232 < baseStart_1842232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842272 : List Nat := [2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 6]
def baseStart_1842272 : Nat := 118140960795 + 1842272 * 2 ^ 59
def prefixEnd_1842272 : Nat := 4983230072969 + 3 ^ 40 * 1842272 * 2
def baseEnd_1842272 : Nat := 945971032319921336027551

theorem tailTrace_1842272 : CollatzResearch.WordTrace tailWord_1842272 prefixEnd_1842272 945971032319921336027551 := by
  unfold tailWord_1842272
  simp only [CollatzResearch.WordTrace]
  refine ⟨33596589990885326926668535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44795453321180435902224713 33596589990885326926668535)
  ·
    refine ⟨50394884986327990390002803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33596589990885326926668535 50394884986327990390002803)
    ·
      refine ⟨75592327479491985585004205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50394884986327990390002803 75592327479491985585004205)
      ·
        refine ⟨28347122804809494594376577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75592327479491985585004205 28347122804809494594376577)
        ·
          refine ⟨21260342103607120945782433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28347122804809494594376577 21260342103607120945782433)
          ·
            refine ⟨15945256577705340709336825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21260342103607120945782433 15945256577705340709336825)
            ·
              refine ⟨11958942433279005532002619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15945256577705340709336825 11958942433279005532002619)
              ·
                refine ⟨17938413649918508298003929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11958942433279005532002619 17938413649918508298003929)
                ·
                  refine ⟨13453810237438881223502947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17938413649918508298003929 13453810237438881223502947)
                  ·
                    refine ⟨20180715356158321835254421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13453810237438881223502947 20180715356158321835254421)
                    ·
                      refine ⟨945971032319921336027551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20180715356158321835254421 945971032319921336027551)
                      ·
                        rfl

theorem cell23_1842272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_1842272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1842272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1842272 prefixEnd_1842272 := by exact prefixLift 1842272
  have htrace : WordTrace (prefixWord ++ tailWord_1842272) baseStart_1842272 baseEnd_1842272 := by
    simpa [prefixWord, tailWord_1842272, baseEnd_1842272] using wordTrace_append hprefix tailTrace_1842272
  have hstable : (prefixWord ++ tailWord_1842272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842272).length < 2 ^ (prefixWord ++ tailWord_1842272).sum := by decide
  have hdescent : baseEnd_1842272 < baseStart_1842272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842336 : List Nat := [2, 1, 1, 4, 2, 1, 2, 1, 4, 3, 2]
def baseStart_1842336 : Nat := 118140960795 + 1842336 * 2 ^ 59
def prefixEnd_1842336 : Nat := 4983230072969 + 3 ^ 40 * 1842336 * 2
def baseEnd_1842336 : Nat := 946003895081809085627257

theorem tailTrace_1842336 : CollatzResearch.WordTrace tailWord_1842336 prefixEnd_1842336 946003895081809085627257 := by
  unfold tailWord_1842336
  simp only [CollatzResearch.WordTrace]
  refine ⟨33597757126769396391833431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44797009502359195189111241 33597757126769396391833431)
  ·
    refine ⟨50396635690154094587750147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33597757126769396391833431 50396635690154094587750147)
    ·
      refine ⟨75594953535231141881625221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50396635690154094587750147 75594953535231141881625221)
      ·
        refine ⟨14174053787855839102804729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75594953535231141881625221 14174053787855839102804729)
        ·
          refine ⟨10630540340891879327103547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14174053787855839102804729 10630540340891879327103547)
          ·
            refine ⟨15945810511337818990655321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10630540340891879327103547 15945810511337818990655321)
            ·
              refine ⟨11959357883503364242991491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15945810511337818990655321 11959357883503364242991491)
              ·
                refine ⟨17939036825255046364487237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11959357883503364242991491 17939036825255046364487237)
                ·
                  refine ⟨3363569404735321193341357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17939036825255046364487237 3363569404735321193341357)
                  ·
                    refine ⟨1261338526775745447503009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3363569404735321193341357 1261338526775745447503009)
                    ·
                      refine ⟨946003895081809085627257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1261338526775745447503009 946003895081809085627257)
                      ·
                        rfl

theorem cell23_1842336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 4, 3, 2].length) (baseStart_1842336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1842336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1842336 prefixEnd_1842336 := by exact prefixLift 1842336
  have htrace : WordTrace (prefixWord ++ tailWord_1842336) baseStart_1842336 baseEnd_1842336 := by
    simpa [prefixWord, tailWord_1842336, baseEnd_1842336] using wordTrace_append hprefix tailTrace_1842336
  have hstable : (prefixWord ++ tailWord_1842336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842336).length < 2 ^ (prefixWord ++ tailWord_1842336).sum := by decide
  have hdescent : baseEnd_1842336 < baseStart_1842336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842343 : List Nat := [1, 1, 6, 2, 1, 1, 1, 3, 3, 1, 3]
def baseStart_1842343 : Nat := 118140960795 + 1842343 * 2 ^ 59
def prefixEnd_1842343 : Nat := 4983230072969 + 3 ^ 40 * 1842343 * 2
def baseEnd_1842343 : Nat := 946007489446390558239725

theorem tailTrace_1842343 : CollatzResearch.WordTrace tailWord_1842343 prefixEnd_1842343 946007489446390558239725 := by
  unfold tailWord_1842343
  simp only [CollatzResearch.WordTrace]
  refine ⟨67195769564513432979171683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44797179709675621986114455 67195769564513432979171683)
  ·
    refine ⟨100793654346770149468757525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67195769564513432979171683 100793654346770149468757525)
    ·
      refine ⟨4724702547504850756348009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 100793654346770149468757525 4724702547504850756348009)
      ·
        refine ⟨3543526910628638067261007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4724702547504850756348009 3543526910628638067261007)
        ·
          refine ⟨5315290365942957100891511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3543526910628638067261007 5315290365942957100891511)
          ·
            refine ⟨7972935548914435651337267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5315290365942957100891511 7972935548914435651337267)
            ·
              refine ⟨11959403323371653477005901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7972935548914435651337267 11959403323371653477005901)
              ·
                refine ⟨4484776246264370053877213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11959403323371653477005901 4484776246264370053877213)
                ·
                  refine ⟨1681791092349138770203955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4484776246264370053877213 1681791092349138770203955)
                  ·
                    refine ⟨2522686638523708155305933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1681791092349138770203955 2522686638523708155305933)
                    ·
                      refine ⟨946007489446390558239725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2522686638523708155305933 946007489446390558239725)
                      ·
                        rfl

theorem cell23_1842343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_1842343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1842343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1842343 prefixEnd_1842343 := by exact prefixLift 1842343
  have htrace : WordTrace (prefixWord ++ tailWord_1842343) baseStart_1842343 baseEnd_1842343 := by
    simpa [prefixWord, tailWord_1842343, baseEnd_1842343] using wordTrace_append hprefix tailTrace_1842343
  have hstable : (prefixWord ++ tailWord_1842343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842343).length < 2 ^ (prefixWord ++ tailWord_1842343).sum := by decide
  have hdescent : baseEnd_1842343 < baseStart_1842343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842386 : List Nat := [3, 2, 2, 2, 1, 1, 4, 1, 1, 1, 5]
def baseStart_1842386 : Nat := 118140960795 + 1842386 * 2 ^ 59
def prefixEnd_1842386 : Nat := 4983230072969 + 3 ^ 40 * 1842386 * 2
def baseEnd_1842386 : Nat := 946029569114533890002027

theorem tailTrace_1842386 : CollatzResearch.WordTrace tailWord_1842386 prefixEnd_1842386 946029569114533890002027 := by
  unfold tailWord_1842386
  simp only [CollatzResearch.WordTrace]
  refine ⟨16799334475839412830746753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44798225268905100881991341 16799334475839412830746753)
  ·
    refine ⟨12599500856879559623060065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16799334475839412830746753 12599500856879559623060065)
    ·
      refine ⟨9449625642659669717295049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12599500856879559623060065 9449625642659669717295049)
      ·
        refine ⟨7087219231994752287971287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9449625642659669717295049 7087219231994752287971287)
        ·
          refine ⟨10630828847992128431956931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7087219231994752287971287 10630828847992128431956931)
          ·
            refine ⟨15946243271988192647935397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10630828847992128431956931 15946243271988192647935397)
            ·
              refine ⟨2989920613497786121487887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15946243271988192647935397 2989920613497786121487887)
              ·
                refine ⟨4484880920246679182231831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2989920613497786121487887 4484880920246679182231831)
                ·
                  refine ⟨6727321380370018773347747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4484880920246679182231831 6727321380370018773347747)
                  ·
                    refine ⟨10090982070555028160021621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6727321380370018773347747 10090982070555028160021621)
                    ·
                      refine ⟨946029569114533890002027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10090982070555028160021621 946029569114533890002027)
                      ·
                        rfl

theorem cell23_1842386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_1842386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1842386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1842386 prefixEnd_1842386 := by exact prefixLift 1842386
  have htrace : WordTrace (prefixWord ++ tailWord_1842386) baseStart_1842386 baseEnd_1842386 := by
    simpa [prefixWord, tailWord_1842386, baseEnd_1842386] using wordTrace_append hprefix tailTrace_1842386
  have hstable : (prefixWord ++ tailWord_1842386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842386).length < 2 ^ (prefixWord ++ tailWord_1842386).sum := by decide
  have hdescent : baseEnd_1842386 < baseStart_1842386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842389 : List Nat := [1, 3, 2, 4, 1, 1, 11]
def baseStart_1842389 : Nat := 118140960795 + 1842389 * 2 ^ 59
def prefixEnd_1842389 : Nat := 4983230072969 + 3 ^ 40 * 1842389 * 2
def baseEnd_1842389 : Nat := 11679396414277745410673

theorem tailTrace_1842389 : CollatzResearch.WordTrace tailWord_1842389 prefixEnd_1842389 11679396414277745410673 := by
  unfold tailWord_1842389
  simp only [CollatzResearch.WordTrace]
  refine ⟨67197447322346782835346221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44798298214897855223564147 67197447322346782835346221)
  ·
    refine ⟨25199042745880043563254833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67197447322346782835346221 25199042745880043563254833)
    ·
      refine ⟨18899282059410032672441125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25199042745880043563254833 18899282059410032672441125)
      ·
        refine ⟨3543615386139381126082711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18899282059410032672441125 3543615386139381126082711)
        ·
          refine ⟨5315423079209071689124067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3543615386139381126082711 5315423079209071689124067)
          ·
            refine ⟨7973134618813607533686101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5315423079209071689124067 7973134618813607533686101)
            ·
              refine ⟨11679396414277745410673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 7973134618813607533686101 11679396414277745410673)
              ·
                rfl

theorem cell23_1842389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 11].length) (baseStart_1842389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1842389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1842389 prefixEnd_1842389 := by exact prefixLift 1842389
  have htrace : WordTrace (prefixWord ++ tailWord_1842389) baseStart_1842389 baseEnd_1842389 := by
    simpa [prefixWord, tailWord_1842389, baseEnd_1842389] using wordTrace_append hprefix tailTrace_1842389
  have hstable : (prefixWord ++ tailWord_1842389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842389).length < 2 ^ (prefixWord ++ tailWord_1842389).sum := by decide
  have hdescent : baseEnd_1842389 < baseStart_1842389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842400 : List Nat := [2, 1, 1, 3, 1, 6, 1, 1, 3, 2, 2]
def baseStart_1842400 : Nat := 118140960795 + 1842400 * 2 ^ 59
def prefixEnd_1842400 : Nat := 4983230072969 + 3 ^ 40 * 1842400 * 2
def baseEnd_1842400 : Nat := 946036757843696835226963

theorem tailTrace_1842400 : CollatzResearch.WordTrace tailWord_1842400 prefixEnd_1842400 946036757843696835226963 := by
  unfold tailWord_1842400
  simp only [CollatzResearch.WordTrace]
  refine ⟨33598924262653465856998327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44798565683537954475997769 33598924262653465856998327)
  ·
    refine ⟨50398386393980198785497491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33598924262653465856998327 50398386393980198785497491)
    ·
      refine ⟨75597579590970298178246237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50398386393980198785497491 75597579590970298178246237)
      ·
        refine ⟨28349092346613861816842339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75597579590970298178246237 28349092346613861816842339)
        ·
          refine ⟨42523638519920792725263509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28349092346613861816842339 42523638519920792725263509)
          ·
            refine ⟨1993295555621287158996727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 42523638519920792725263509 1993295555621287158996727)
            ·
              refine ⟨2989943333431930738495091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1993295555621287158996727 2989943333431930738495091)
              ·
                refine ⟨4484915000147896107742637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2989943333431930738495091 4484915000147896107742637)
                ·
                  refine ⟨1681843125055461040403489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4484915000147896107742637 1681843125055461040403489)
                  ·
                    refine ⟨1261382343791595780302617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1681843125055461040403489 1261382343791595780302617)
                    ·
                      refine ⟨946036757843696835226963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1261382343791595780302617 946036757843696835226963)
                      ·
                        rfl

theorem cell23_1842400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 1, 3, 2, 2].length) (baseStart_1842400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1842400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1842400 prefixEnd_1842400 := by exact prefixLift 1842400
  have htrace : WordTrace (prefixWord ++ tailWord_1842400) baseStart_1842400 baseEnd_1842400 := by
    simpa [prefixWord, tailWord_1842400, baseEnd_1842400] using wordTrace_append hprefix tailTrace_1842400
  have hstable : (prefixWord ++ tailWord_1842400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842400).length < 2 ^ (prefixWord ++ tailWord_1842400).sum := by decide
  have hdescent : baseEnd_1842400 < baseStart_1842400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842410 : List Nat := [3, 1, 3, 1, 1, 5, 2, 1, 2, 4]
def baseStart_1842410 : Nat := 118140960795 + 1842410 * 2 ^ 59
def prefixEnd_1842410 : Nat := 4983230072969 + 3 ^ 40 * 1842410 * 2
def baseEnd_1842410 : Nat := 315347297550080598700639

theorem tailTrace_1842410 : CollatzResearch.WordTrace tailWord_1842410 prefixEnd_1842410 315347297550080598700639 := by
  unfold tailWord_1842410
  simp only [CollatzResearch.WordTrace]
  refine ⟨16799553313817675855465171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44798808836847135614573789 16799553313817675855465171)
  ·
    refine ⟨25199329970726513783197757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16799553313817675855465171 25199329970726513783197757)
    ·
      refine ⟨9449748739022442668699159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25199329970726513783197757 9449748739022442668699159)
      ·
        refine ⟨14174623108533664003048739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9449748739022442668699159 14174623108533664003048739)
        ·
          refine ⟨21261934662800496004573109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14174623108533664003048739 21261934662800496004573109)
          ·
            refine ⟨1993306374637546500428729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21261934662800496004573109 1993306374637546500428729)
            ·
              refine ⟨1494979780978159875321547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1993306374637546500428729 1494979780978159875321547)
              ·
                refine ⟨2242469671467239812982321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1494979780978159875321547 2242469671467239812982321)
                ·
                  refine ⟨1681852253600429859736741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2242469671467239812982321 1681852253600429859736741)
                  ·
                    refine ⟨315347297550080598700639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1681852253600429859736741 315347297550080598700639)
                    ·
                      rfl

theorem cell23_1842410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 1, 2, 4].length) (baseStart_1842410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1842410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1842410 prefixEnd_1842410 := by exact prefixLift 1842410
  have htrace : WordTrace (prefixWord ++ tailWord_1842410) baseStart_1842410 baseEnd_1842410 := by
    simpa [prefixWord, tailWord_1842410, baseEnd_1842410] using wordTrace_append hprefix tailTrace_1842410
  have hstable : (prefixWord ++ tailWord_1842410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842410).length < 2 ^ (prefixWord ++ tailWord_1842410).sum := by decide
  have hdescent : baseEnd_1842410 < baseStart_1842410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842449 : List Nat := [1, 2, 2, 1, 1, 4, 2, 2, 2, 6]
def baseStart_1842449 : Nat := 118140960795 + 1842449 * 2 ^ 59
def prefixEnd_1842449 : Nat := 4983230072969 + 3 ^ 40 * 1842449 * 2
def baseEnd_1842449 : Nat := 315353972798589047838079

theorem tailTrace_1842449 : CollatzResearch.WordTrace tailWord_1842449 prefixEnd_1842449 315353972798589047838079 := by
  unfold tailWord_1842449
  simp only [CollatzResearch.WordTrace]
  refine ⟨67199635702129413082530401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44799757134752942055020267 67199635702129413082530401)
  ·
    refine ⟨50399726776597059811897801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67199635702129413082530401 50399726776597059811897801)
    ·
      refine ⟨37799795082447794858923351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50399726776597059811897801 37799795082447794858923351)
      ·
        refine ⟨56699692623671692288385027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37799795082447794858923351 56699692623671692288385027)
        ·
          refine ⟨85049538935507538432577541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56699692623671692288385027 85049538935507538432577541)
          ·
            refine ⟨15946788550407663456108289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85049538935507538432577541 15946788550407663456108289)
            ·
              refine ⟨11960091412805747592081217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15946788550407663456108289 11960091412805747592081217)
              ·
                refine ⟨8970068559604310694060913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11960091412805747592081217 8970068559604310694060913)
                ·
                  refine ⟨6727551419703233020545685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8970068559604310694060913 6727551419703233020545685)
                  ·
                    refine ⟨315353972798589047838079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6727551419703233020545685 315353972798589047838079)
                    ·
                      rfl

theorem cell23_1842449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 6].length) (baseStart_1842449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1842449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1842449 prefixEnd_1842449 := by exact prefixLift 1842449
  have htrace : WordTrace (prefixWord ++ tailWord_1842449) baseStart_1842449 baseEnd_1842449 := by
    simpa [prefixWord, tailWord_1842449, baseEnd_1842449] using wordTrace_append hprefix tailTrace_1842449
  have hstable : (prefixWord ++ tailWord_1842449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842449).length < 2 ^ (prefixWord ++ tailWord_1842449).sum := by decide
  have hdescent : baseEnd_1842449 < baseStart_1842449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842518 : List Nat := [5, 2, 3, 1, 1, 1, 3, 1, 2, 1, 3]
def baseStart_1842518 : Nat := 118140960795 + 1842518 * 2 ^ 59
def prefixEnd_1842518 : Nat := 4983230072969 + 3 ^ 40 * 1842518 * 2
def baseEnd_1842518 : Nat := 946097348560927373551421

theorem tailTrace_1842518 : CollatzResearch.WordTrace tailWord_1842518 prefixEnd_1842518 946097348560927373551421 := by
  unfold tailWord_1842518
  simp only [CollatzResearch.WordTrace]
  refine ⟨4200134521179964866674513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44801434892586291911194805 4200134521179964866674513)
  ·
    refine ⟨3150100890884973650005885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4200134521179964866674513 3150100890884973650005885)
    ·
      refine ⟨1181287834081865118752207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3150100890884973650005885 1181287834081865118752207)
      ·
        refine ⟨1771931751122797678128311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1181287834081865118752207 1771931751122797678128311)
        ·
          refine ⟨2657897626684196517192467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1771931751122797678128311 2657897626684196517192467)
          ·
            refine ⟨3986846440026294775788701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2657897626684196517192467 3986846440026294775788701)
            ·
              refine ⟨1495067415009860540920763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3986846440026294775788701 1495067415009860540920763)
              ·
                refine ⟨2242601122514790811381145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1495067415009860540920763 2242601122514790811381145)
                ·
                  refine ⟨1681950841886093108535859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2242601122514790811381145 1681950841886093108535859)
                  ·
                    refine ⟨2522926262829139662803789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1681950841886093108535859 2522926262829139662803789)
                    ·
                      refine ⟨946097348560927373551421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2522926262829139662803789 946097348560927373551421)
                      ·
                        rfl

theorem cell23_1842518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_1842518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1842518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1842518 prefixEnd_1842518 := by exact prefixLift 1842518
  have htrace : WordTrace (prefixWord ++ tailWord_1842518) baseStart_1842518 baseEnd_1842518 := by
    simpa [prefixWord, tailWord_1842518, baseEnd_1842518] using wordTrace_append hprefix tailTrace_1842518
  have hstable : (prefixWord ++ tailWord_1842518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842518).length < 2 ^ (prefixWord ++ tailWord_1842518).sum := by decide
  have hdescent : baseEnd_1842518 < baseStart_1842518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842546 : List Nat := [3, 2, 1, 2, 1, 2, 1, 3, 1, 3, 4]
def baseStart_1842546 : Nat := 118140960795 + 1842546 * 2 ^ 59
def prefixEnd_1842546 : Nat := 4983230072969 + 3 ^ 40 * 1842546 * 2
def baseEnd_1842546 : Nat := 946111726019253264001291

theorem tailTrace_1842546 : CollatzResearch.WordTrace tailWord_1842546 prefixEnd_1842546 946111726019253264001291 := by
  unfold tailWord_1842546
  simp only [CollatzResearch.WordTrace]
  refine ⟨16800793395694499662202873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44802115721851999099207661 16800793395694499662202873)
  ·
    refine ⟨12600595046770874746652155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16800793395694499662202873 12600595046770874746652155)
    ·
      refine ⟨18900892570156312119978233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12600595046770874746652155 18900892570156312119978233)
      ·
        refine ⟨14175669427617234089983675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18900892570156312119978233 14175669427617234089983675)
        ·
          refine ⟨21263504141425851134975513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14175669427617234089983675 21263504141425851134975513)
          ·
            refine ⟨15947628106069388351231635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21263504141425851134975513 15947628106069388351231635)
            ·
              refine ⟨23921442159104082526847453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15947628106069388351231635 23921442159104082526847453)
              ·
                refine ⟨8970540809664030947567795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23921442159104082526847453 8970540809664030947567795)
                ·
                  refine ⟨13455811214496046421351693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8970540809664030947567795 13455811214496046421351693)
                  ·
                    refine ⟨5045929205436017408006885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13455811214496046421351693 5045929205436017408006885)
                    ·
                      refine ⟨946111726019253264001291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5045929205436017408006885 946111726019253264001291)
                      ·
                        rfl

theorem cell23_1842546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_1842546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1842546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1842546 prefixEnd_1842546 := by exact prefixLift 1842546
  have htrace : WordTrace (prefixWord ++ tailWord_1842546) baseStart_1842546 baseEnd_1842546 := by
    simpa [prefixWord, tailWord_1842546, baseEnd_1842546] using wordTrace_append hprefix tailTrace_1842546
  have hstable : (prefixWord ++ tailWord_1842546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842546).length < 2 ^ (prefixWord ++ tailWord_1842546).sum := by decide
  have hdescent : baseEnd_1842546 < baseStart_1842546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842563 : List Nat := [1, 1, 1, 3, 5, 2, 1, 2, 2, 1, 4]
def baseStart_1842563 : Nat := 118140960795 + 1842563 * 2 ^ 59
def prefixEnd_1842563 : Nat := 4983230072969 + 3 ^ 40 * 1842563 * 2
def baseEnd_1842563 : Nat := 946120455190379697488713

theorem tailTrace_1842563 : CollatzResearch.WordTrace tailWord_1842563 prefixEnd_1842563 946120455190379697488713 := by
  unfold tailWord_1842563
  simp only [CollatzResearch.WordTrace]
  refine ⟨67203793623716410552180343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44802529082477607034786895 67203793623716410552180343)
  ·
    refine ⟨100805690435574615828270515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67203793623716410552180343 100805690435574615828270515)
    ·
      refine ⟨151208535653361923742405773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100805690435574615828270515 151208535653361923742405773)
      ·
        refine ⟨56703200870010721403402165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151208535653361923742405773 56703200870010721403402165)
        ·
          refine ⟨5315925081563505131568953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56703200870010721403402165 5315925081563505131568953)
          ·
            refine ⟨3986943811172628848676715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5315925081563505131568953 3986943811172628848676715)
            ·
              refine ⟨5980415716758943273015073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3986943811172628848676715 5980415716758943273015073)
              ·
                refine ⟨4485311787569207454761305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5980415716758943273015073 4485311787569207454761305)
                ·
                  refine ⟨3363983840676905591070979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4485311787569207454761305 3363983840676905591070979)
                  ·
                    refine ⟨5045975761015358386606469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3363983840676905591070979 5045975761015358386606469)
                    ·
                      refine ⟨946120455190379697488713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5045975761015358386606469 946120455190379697488713)
                      ·
                        rfl

theorem cell23_1842563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 2, 2, 1, 4].length) (baseStart_1842563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1842563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1842563 prefixEnd_1842563 := by exact prefixLift 1842563
  have htrace : WordTrace (prefixWord ++ tailWord_1842563) baseStart_1842563 baseEnd_1842563 := by
    simpa [prefixWord, tailWord_1842563, baseEnd_1842563] using wordTrace_append hprefix tailTrace_1842563
  have hstable : (prefixWord ++ tailWord_1842563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842563).length < 2 ^ (prefixWord ++ tailWord_1842563).sum := by decide
  have hdescent : baseEnd_1842563 < baseStart_1842563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842620 : List Nat := [2, 2, 2, 4, 2, 1, 2, 2, 6]
def baseStart_1842620 : Nat := 118140960795 + 1842620 * 2 ^ 59
def prefixEnd_1842620 : Nat := 4983230072969 + 3 ^ 40 * 1842620 * 2
def baseEnd_1842620 : Nat := 105127747065298441608439

theorem tailTrace_1842620 : CollatzResearch.WordTrace tailWord_1842620 prefixEnd_1842620 105127747065298441608439 := by
  unfold tailWord_1842620
  simp only [CollatzResearch.WordTrace]
  refine ⟨33602936292254954643502657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44803915056339939524670209 33602936292254954643502657)
  ·
    refine ⟨25202202219191215982626993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33602936292254954643502657 25202202219191215982626993)
    ·
      refine ⟨18901651664393411986970245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25202202219191215982626993 18901651664393411986970245)
      ·
        refine ⟨3544059687073764747556921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18901651664393411986970245 3544059687073764747556921)
        ·
          refine ⟨2658044765305323560667691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3544059687073764747556921 2658044765305323560667691)
          ·
            refine ⟨3987067147957985341001537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2658044765305323560667691 3987067147957985341001537)
            ·
              refine ⟨2990300360968489005751153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3987067147957985341001537 2990300360968489005751153)
              ·
                refine ⟨2242725270726366754313365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2990300360968489005751153 2242725270726366754313365)
                ·
                  refine ⟨105127747065298441608439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2242725270726366754313365 105127747065298441608439)
                  ·
                    rfl

theorem cell23_1842620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 2, 6].length) (baseStart_1842620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1842620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1842620 prefixEnd_1842620 := by exact prefixLift 1842620
  have htrace : WordTrace (prefixWord ++ tailWord_1842620) baseStart_1842620 baseEnd_1842620 := by
    simpa [prefixWord, tailWord_1842620, baseEnd_1842620] using wordTrace_append hprefix tailTrace_1842620
  have hstable : (prefixWord ++ tailWord_1842620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842620).length < 2 ^ (prefixWord ++ tailWord_1842620).sum := by decide
  have hdescent : baseEnd_1842620 < baseStart_1842620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842656 : List Nat := [2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 5]
def baseStart_1842656 : Nat := 118140960795 + 1842656 * 2 ^ 59
def prefixEnd_1842656 : Nat := 4983230072969 + 3 ^ 40 * 1842656 * 2
def baseEnd_1842656 : Nat := 946168208891247833625785

theorem tailTrace_1842656 : CollatzResearch.WordTrace tailWord_1842656 prefixEnd_1842656 946168208891247833625785 := by
  unfold tailWord_1842656
  simp only [CollatzResearch.WordTrace]
  refine ⟨33603592806189743717657911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44804790408252991623543881 33603592806189743717657911)
  ·
    refine ⟨50405389209284615576486867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33603592806189743717657911 50405389209284615576486867)
    ·
      refine ⟨75608083813926923364730301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50405389209284615576486867 75608083813926923364730301)
      ·
        refine ⟨28353031430222596261773863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75608083813926923364730301 28353031430222596261773863)
        ·
          refine ⟨42529547145333894392660795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28353031430222596261773863 42529547145333894392660795)
          ·
            refine ⟨63794320718000841588991193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42529547145333894392660795 63794320718000841588991193)
            ·
              refine ⟨47845740538500631191743395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63794320718000841588991193 47845740538500631191743395)
              ·
                refine ⟨71768610807750946787615093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47845740538500631191743395 71768610807750946787615093)
                ·
                  refine ⟨6728307263226651261338915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71768610807750946787615093 6728307263226651261338915)
                  ·
                    refine ⟨10092460894839976892008373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6728307263226651261338915 10092460894839976892008373)
                    ·
                      refine ⟨946168208891247833625785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10092460894839976892008373 946168208891247833625785)
                      ·
                        rfl

theorem cell23_1842656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_1842656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1842656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1842656 prefixEnd_1842656 := by exact prefixLift 1842656
  have htrace : WordTrace (prefixWord ++ tailWord_1842656) baseStart_1842656 baseEnd_1842656 := by
    simpa [prefixWord, tailWord_1842656, baseEnd_1842656] using wordTrace_append hprefix tailTrace_1842656
  have hstable : (prefixWord ++ tailWord_1842656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842656).length < 2 ^ (prefixWord ++ tailWord_1842656).sum := by decide
  have hdescent : baseEnd_1842656 < baseStart_1842656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842657 : List Nat := [1, 2, 3, 1, 2, 5, 1, 1, 2, 3, 2]
def baseStart_1842657 : Nat := 118140960795 + 1842657 * 2 ^ 59
def prefixEnd_1842657 : Nat := 4983230072969 + 3 ^ 40 * 1842657 * 2
def baseEnd_1842657 : Nat := 946168722371902329713281

theorem tailTrace_1842657 : CollatzResearch.WordTrace tailWord_1842657 prefixEnd_1842657 946168722371902329713281 := by
  unfold tailWord_1842657
  simp only [CollatzResearch.WordTrace]
  refine ⟨67207222085375864606102225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44804814723583909737401483 67207222085375864606102225)
  ·
    refine ⟨50405416564031898454576669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67207222085375864606102225 50405416564031898454576669)
    ·
      refine ⟨18902031211511961920466251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50405416564031898454576669 18902031211511961920466251)
      ·
        refine ⟨28353046817267942880699377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18902031211511961920466251 28353046817267942880699377)
        ·
          refine ⟨21264785112950957160524533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28353046817267942880699377 21264785112950957160524533)
          ·
            refine ⟨1993573604339152233799175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21264785112950957160524533 1993573604339152233799175)
            ·
              refine ⟨2990360406508728350698763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1993573604339152233799175 2990360406508728350698763)
              ·
                refine ⟨4485540609763092526048145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2990360406508728350698763 4485540609763092526048145)
                ·
                  refine ⟨3364155457322319394536109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4485540609763092526048145 3364155457322319394536109)
                  ·
                    refine ⟨1261558296495869772951041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3364155457322319394536109 1261558296495869772951041)
                    ·
                      refine ⟨946168722371902329713281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1261558296495869772951041 946168722371902329713281)
                      ·
                        rfl

theorem cell23_1842657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 1, 2, 3, 2].length) (baseStart_1842657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1842657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1842657 prefixEnd_1842657 := by exact prefixLift 1842657
  have htrace : WordTrace (prefixWord ++ tailWord_1842657) baseStart_1842657 baseEnd_1842657 := by
    simpa [prefixWord, tailWord_1842657, baseEnd_1842657] using wordTrace_append hprefix tailTrace_1842657
  have hstable : (prefixWord ++ tailWord_1842657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842657).length < 2 ^ (prefixWord ++ tailWord_1842657).sum := by decide
  have hdescent : baseEnd_1842657 < baseStart_1842657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842663 : List Nat := [1, 1, 5, 2, 1, 2, 2, 2, 1, 6]
def baseStart_1842663 : Nat := 118140960795 + 1842663 * 2 ^ 59
def prefixEnd_1842663 : Nat := 4983230072969 + 3 ^ 40 * 1842663 * 2
def baseEnd_1842663 : Nat := 315390601085276435412751

theorem tailTrace_1842663 : CollatzResearch.WordTrace tailWord_1842663 prefixEnd_1842663 315390601085276435412751 := by
  unfold tailWord_1842663
  simp only [CollatzResearch.WordTrace]
  refine ⟨67207440923354127630820643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44804960615569418420547095 67207440923354127630820643)
  ·
    refine ⟨100811161385031191446230965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67207440923354127630820643 100811161385031191446230965)
    ·
      refine ⟨9451046379846674198084153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100811161385031191446230965 9451046379846674198084153)
      ·
        refine ⟨7088284784885005648563115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9451046379846674198084153 7088284784885005648563115)
        ·
          refine ⟨10632427177327508472844673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7088284784885005648563115 10632427177327508472844673)
          ·
            refine ⟨7974320382995631354633505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10632427177327508472844673 7974320382995631354633505)
            ·
              refine ⟨5980740287246723515975129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7974320382995631354633505 5980740287246723515975129)
              ·
                refine ⟨4485555215435042636981347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5980740287246723515975129 4485555215435042636981347)
                ·
                  refine ⟨6728332823152563955472021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4485555215435042636981347 6728332823152563955472021)
                  ·
                    refine ⟨315390601085276435412751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6728332823152563955472021 315390601085276435412751)
                    ·
                      rfl

theorem cell23_1842663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_1842663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1842663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1842663 prefixEnd_1842663 := by exact prefixLift 1842663
  have htrace : WordTrace (prefixWord ++ tailWord_1842663) baseStart_1842663 baseEnd_1842663 := by
    simpa [prefixWord, tailWord_1842663, baseEnd_1842663] using wordTrace_append hprefix tailTrace_1842663
  have hstable : (prefixWord ++ tailWord_1842663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842663).length < 2 ^ (prefixWord ++ tailWord_1842663).sum := by decide
  have hdescent : baseEnd_1842663 < baseStart_1842663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842670 : List Nat := [4, 1, 2, 1, 2, 1, 3, 3, 1, 1, 4]
def baseStart_1842670 : Nat := 118140960795 + 1842670 * 2 ^ 59
def prefixEnd_1842670 : Nat := 4983230072969 + 3 ^ 40 * 1842670 * 2
def baseEnd_1842670 : Nat := 946175397620410778850721

theorem tailTrace_1842670 : CollatzResearch.WordTrace tailWord_1842670 prefixEnd_1842670 946175397620410778850721 := by
  unfold tailWord_1842670
  simp only [CollatzResearch.WordTrace]
  refine ⟨8400962029291095978290683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44805130822885845217550309 8400962029291095978290683)
  ·
    refine ⟨12601443043936643967436025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8400962029291095978290683 12601443043936643967436025)
    ·
      refine ⟨9451082282952482975577019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12601443043936643967436025 9451082282952482975577019)
      ·
        refine ⟨14176623424428724463365529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9451082282952482975577019 14176623424428724463365529)
        ·
          refine ⟨10632467568321543347524147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14176623424428724463365529 10632467568321543347524147)
          ·
            refine ⟨15948701352482315021286221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10632467568321543347524147 15948701352482315021286221)
            ·
              refine ⟨5980763007180868132982333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15948701352482315021286221 5980763007180868132982333)
              ·
                refine ⟨2242786127692825549868375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5980763007180868132982333 2242786127692825549868375)
                ·
                  refine ⟨3364179191539238324802563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2242786127692825549868375 3364179191539238324802563)
                  ·
                    refine ⟨5046268787308857487203845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3364179191539238324802563 5046268787308857487203845)
                    ·
                      refine ⟨946175397620410778850721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5046268787308857487203845 946175397620410778850721)
                      ·
                        rfl

theorem cell23_1842670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_1842670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1842670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1842670 prefixEnd_1842670 := by exact prefixLift 1842670
  have htrace : WordTrace (prefixWord ++ tailWord_1842670) baseStart_1842670 baseEnd_1842670 := by
    simpa [prefixWord, tailWord_1842670, baseEnd_1842670] using wordTrace_append hprefix tailTrace_1842670
  have hstable : (prefixWord ++ tailWord_1842670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842670).length < 2 ^ (prefixWord ++ tailWord_1842670).sum := by decide
  have hdescent : baseEnd_1842670 < baseStart_1842670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842680 : List Nat := [2, 1, 2, 1, 1, 5, 3, 2, 2, 4]
def baseStart_1842680 : Nat := 118140960795 + 1842680 * 2 ^ 59
def prefixEnd_1842680 : Nat := 4983230072969 + 3 ^ 40 * 1842680 * 2
def baseEnd_1842680 : Nat := 315393510808985246575225

theorem tailTrace_1842680 : CollatzResearch.WordTrace tailWord_1842680 prefixEnd_1842680 315393510808985246575225 := by
  unfold tailWord_1842680
  simp only [CollatzResearch.WordTrace]
  refine ⟨33604030482146269767094747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44805373976195026356126329 33604030482146269767094747)
  ·
    refine ⟨50406045723219404650642121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33604030482146269767094747 50406045723219404650642121)
    ·
      refine ⟨37804534292414553487981591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50406045723219404650642121 37804534292414553487981591)
      ·
        refine ⟨56706801438621830231972387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37804534292414553487981591 56706801438621830231972387)
        ·
          refine ⟨85060202157932745347958581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56706801438621830231972387 85060202157932745347958581)
          ·
            refine ⟨7974393952306194876371117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85060202157932745347958581 7974393952306194876371117)
            ·
              refine ⟨2990397732114823078639169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7974393952306194876371117 2990397732114823078639169)
              ·
                refine ⟨2242798299086117308979377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2990397732114823078639169 2242798299086117308979377)
                ·
                  refine ⟨1682098724314587981734533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2242798299086117308979377 1682098724314587981734533)
                  ·
                    refine ⟨315393510808985246575225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1682098724314587981734533 315393510808985246575225)
                    ·
                      rfl

theorem cell23_1842680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 2, 2, 4].length) (baseStart_1842680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1842680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1842680 prefixEnd_1842680 := by exact prefixLift 1842680
  have htrace : WordTrace (prefixWord ++ tailWord_1842680) baseStart_1842680 baseEnd_1842680 := by
    simpa [prefixWord, tailWord_1842680, baseEnd_1842680] using wordTrace_append hprefix tailTrace_1842680
  have hstable : (prefixWord ++ tailWord_1842680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842680).length < 2 ^ (prefixWord ++ tailWord_1842680).sum := by decide
  have hdescent : baseEnd_1842680 < baseStart_1842680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842690 : List Nat := [3, 4, 1, 2, 1, 1, 1, 1, 3, 1, 5]
def baseStart_1842690 : Nat := 118140960795 + 1842690 * 2 ^ 59
def prefixEnd_1842690 : Nat := 4983230072969 + 3 ^ 40 * 1842690 * 2
def baseEnd_1842690 : Nat := 946185667233500700600629

theorem tailTrace_1842690 : CollatzResearch.WordTrace tailWord_1842690 prefixEnd_1842690 946185667233500700600629 := by
  unfold tailWord_1842690
  simp only [CollatzResearch.WordTrace]
  refine ⟨16802106423564077810513381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44805617129504207494702349 16802106423564077810513381)
  ·
    refine ⟨3150394954418264589471259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16802106423564077810513381 3150394954418264589471259)
    ·
      refine ⟨4725592431627396884206889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3150394954418264589471259 4725592431627396884206889)
      ·
        refine ⟨3544194323720547663155167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4725592431627396884206889 3544194323720547663155167)
        ·
          refine ⟨5316291485580821494732751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3544194323720547663155167 5316291485580821494732751)
          ·
            refine ⟨7974437228371232242099127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5316291485580821494732751 7974437228371232242099127)
            ·
              refine ⟨11961655842556848363148691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7974437228371232242099127 11961655842556848363148691)
              ·
                refine ⟨17942483763835272544723037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11961655842556848363148691 17942483763835272544723037)
                ·
                  refine ⟨6728431411438227204271139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17942483763835272544723037 6728431411438227204271139)
                  ·
                    refine ⟨10092647117157340806406709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6728431411438227204271139 10092647117157340806406709)
                    ·
                      refine ⟨946185667233500700600629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10092647117157340806406709 946185667233500700600629)
                      ·
                        rfl

theorem cell23_1842690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_1842690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1842690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1842690 prefixEnd_1842690 := by exact prefixLift 1842690
  have htrace : WordTrace (prefixWord ++ tailWord_1842690) baseStart_1842690 baseEnd_1842690 := by
    simpa [prefixWord, tailWord_1842690, baseEnd_1842690] using wordTrace_append hprefix tailTrace_1842690
  have hstable : (prefixWord ++ tailWord_1842690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842690).length < 2 ^ (prefixWord ++ tailWord_1842690).sum := by decide
  have hdescent : baseEnd_1842690 < baseStart_1842690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842721 : List Nat := [1, 2, 3, 2, 2, 4, 1, 3, 1, 2, 2]
def baseStart_1842721 : Nat := 118140960795 + 1842721 * 2 ^ 59
def prefixEnd_1842721 : Nat := 4983230072969 + 3 ^ 40 * 1842721 * 2
def baseEnd_1842721 : Nat := 946201585133790079312987

theorem tailTrace_1842721 : CollatzResearch.WordTrace tailWord_1842721 prefixEnd_1842721 946201585133790079312987 := by
  unfold tailWord_1842721
  simp only [CollatzResearch.WordTrace]
  refine ⟨67209556357144003536432017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44806370904762669024288011 67209556357144003536432017)
  ·
    refine ⟨50407167267858002652324013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67209556357144003536432017 50407167267858002652324013)
    ·
      refine ⟨18902687725446750994621505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50407167267858002652324013 18902687725446750994621505)
      ·
        refine ⟨14177015794085063245966129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18902687725446750994621505 14177015794085063245966129)
        ·
          refine ⟨10632761845563797434474597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14177015794085063245966129 10632761845563797434474597)
          ·
            refine ⟨1993642846043212018963987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10632761845563797434474597 1993642846043212018963987)
            ·
              refine ⟨2990464269064818028445981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1993642846043212018963987 2990464269064818028445981)
              ·
                refine ⟨1121424100899306760667243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2990464269064818028445981 1121424100899306760667243)
                ·
                  refine ⟨1682136151348960141000865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1121424100899306760667243 1682136151348960141000865)
                  ·
                    refine ⟨1261602113511720105750649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1682136151348960141000865 1261602113511720105750649)
                    ·
                      refine ⟨946201585133790079312987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1261602113511720105750649 946201585133790079312987)
                      ·
                        rfl

theorem cell23_1842721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 3, 1, 2, 2].length) (baseStart_1842721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1842721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1842721 prefixEnd_1842721 := by exact prefixLift 1842721
  have htrace : WordTrace (prefixWord ++ tailWord_1842721) baseStart_1842721 baseEnd_1842721 := by
    simpa [prefixWord, tailWord_1842721, baseEnd_1842721] using wordTrace_append hprefix tailTrace_1842721
  have hstable : (prefixWord ++ tailWord_1842721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842721).length < 2 ^ (prefixWord ++ tailWord_1842721).sum := by decide
  have hdescent : baseEnd_1842721 < baseStart_1842721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842753 : List Nat := [1, 2, 5, 1, 1, 1, 2, 1, 1, 8]
def baseStart_1842753 : Nat := 118140960795 + 1842753 * 2 ^ 59
def prefixEnd_1842753 : Nat := 4983230072969 + 3 ^ 40 * 1842753 * 2
def baseEnd_1842753 : Nat := 315406005504911318037613

theorem tailTrace_1842753 : CollatzResearch.WordTrace tailWord_1842753 prefixEnd_1842753 315406005504911318037613 := by
  unfold tailWord_1842753
  simp only [CollatzResearch.WordTrace]
  refine ⟨67210723493028073001596913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44807148995352048667731275 67210723493028073001596913)
  ·
    refine ⟨50408042619771054751197685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67210723493028073001596913 50408042619771054751197685)
    ·
      refine ⟨4725753995603536382924783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50408042619771054751197685 4725753995603536382924783)
      ·
        refine ⟨7088630993405304574387175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4725753995603536382924783 7088630993405304574387175)
        ·
          refine ⟨10632946490107956861580763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7088630993405304574387175 10632946490107956861580763)
          ·
            refine ⟨15949419735161935292371145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10632946490107956861580763 15949419735161935292371145)
            ·
              refine ⟨11962064801371451469278359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15949419735161935292371145 11962064801371451469278359)
              ·
                refine ⟨17943097202057177203917539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11962064801371451469278359 17943097202057177203917539)
                ·
                  refine ⟨26914645803085765805876309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17943097202057177203917539 26914645803085765805876309)
                  ·
                    refine ⟨315406005504911318037613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 26914645803085765805876309 315406005504911318037613)
                    ·
                      rfl

theorem cell23_1842753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_1842753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1842753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1842753 prefixEnd_1842753 := by exact prefixLift 1842753
  have htrace : WordTrace (prefixWord ++ tailWord_1842753) baseStart_1842753 baseEnd_1842753 := by
    simpa [prefixWord, tailWord_1842753, baseEnd_1842753] using wordTrace_append hprefix tailTrace_1842753
  have hstable : (prefixWord ++ tailWord_1842753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842753).length < 2 ^ (prefixWord ++ tailWord_1842753).sum := by decide
  have hdescent : baseEnd_1842753 < baseStart_1842753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842758 : List Nat := [6, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3]
def baseStart_1842758 : Nat := 118140960795 + 1842758 * 2 ^ 59
def prefixEnd_1842758 : Nat := 4983230072969 + 3 ^ 40 * 1842758 * 2
def baseEnd_1842758 : Nat := 946220583918006434550317

theorem tailTrace_1842758 : CollatzResearch.WordTrace tailWord_1842758 prefixEnd_1842758 946220583918006434550317 := by
  unfold tailWord_1842758
  simp only [CollatzResearch.WordTrace]
  refine ⟨2100340808062811214235279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 44807270572006639237019285 2100340808062811214235279)
  ·
    refine ⟨3150511212094216821352919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2100340808062811214235279 3150511212094216821352919)
    ·
      refine ⟨4725766818141325232029379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3150511212094216821352919 4725766818141325232029379)
      ·
        refine ⟨7088650227211987848044069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4725766818141325232029379 7088650227211987848044069)
        ·
          refine ⟨1329121917602247721508263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7088650227211987848044069 1329121917602247721508263)
          ·
            refine ⟨1993682876403371582262395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1329121917602247721508263 1993682876403371582262395)
            ·
              refine ⟨2990524314605057373393593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1993682876403371582262395 2990524314605057373393593)
              ·
                refine ⟨2242893235953793030045195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2990524314605057373393593 2242893235953793030045195)
                ·
                  refine ⟨3364339853930689545067793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2242893235953793030045195 3364339853930689545067793)
                  ·
                    refine ⟨2523254890448017158800845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3364339853930689545067793 2523254890448017158800845)
                    ·
                      refine ⟨946220583918006434550317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2523254890448017158800845 946220583918006434550317)
                      ·
                        rfl

theorem cell23_1842758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_1842758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1842758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1842758 prefixEnd_1842758 := by exact prefixLift 1842758
  have htrace : WordTrace (prefixWord ++ tailWord_1842758) baseStart_1842758 baseEnd_1842758 := by
    simpa [prefixWord, tailWord_1842758, baseEnd_1842758] using wordTrace_append hprefix tailTrace_1842758
  have hstable : (prefixWord ++ tailWord_1842758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842758).length < 2 ^ (prefixWord ++ tailWord_1842758).sum := by decide
  have hdescent : baseEnd_1842758 < baseStart_1842758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842764 : List Nat := [2, 2, 1, 3, 1, 5, 1, 2, 1, 3, 2]
def baseStart_1842764 : Nat := 118140960795 + 1842764 * 2 ^ 59
def prefixEnd_1842764 : Nat := 4983230072969 + 3 ^ 40 * 1842764 * 2
def baseEnd_1842764 : Nat := 946223664801933411075289

theorem tailTrace_1842764 : CollatzResearch.WordTrace tailWord_1842764 prefixEnd_1842764 946223664801933411075289 := by
  unfold tailWord_1842764
  simp only [CollatzResearch.WordTrace]
  refine ⟨33605562347994110940123673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44807416463992147920164897 33605562347994110940123673)
  ·
    refine ⟨25204171760995583205092755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33605562347994110940123673 25204171760995583205092755)
    ·
      refine ⟨37806257641493374807639133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25204171760995583205092755 37806257641493374807639133)
      ·
        refine ⟨14177346615560015552864675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37806257641493374807639133 14177346615560015552864675)
        ·
          refine ⟨21266019923340023329297013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14177346615560015552864675 21266019923340023329297013)
          ·
            refine ⟨1993689367813127187121595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21266019923340023329297013 1993689367813127187121595)
            ·
              refine ⟨2990534051719690780682393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1993689367813127187121595 2990534051719690780682393)
              ·
                refine ⟨2242900538789768085511795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2990534051719690780682393 2242900538789768085511795)
                ·
                  refine ⟨3364350808184652128267693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2242900538789768085511795 3364350808184652128267693)
                  ·
                    refine ⟨1261631553069244548100385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3364350808184652128267693 1261631553069244548100385)
                    ·
                      refine ⟨946223664801933411075289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1261631553069244548100385 946223664801933411075289)
                      ·
                        rfl

theorem cell23_1842764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 2, 1, 3, 2].length) (baseStart_1842764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1842764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1842764 prefixEnd_1842764 := by exact prefixLift 1842764
  have htrace : WordTrace (prefixWord ++ tailWord_1842764) baseStart_1842764 baseEnd_1842764 := by
    simpa [prefixWord, tailWord_1842764, baseEnd_1842764] using wordTrace_append hprefix tailTrace_1842764
  have hstable : (prefixWord ++ tailWord_1842764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842764).length < 2 ^ (prefixWord ++ tailWord_1842764).sum := by decide
  have hdescent : baseEnd_1842764 < baseStart_1842764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842773 : List Nat := [1, 3, 2, 2, 1, 1, 1, 2, 4, 2, 4]
def baseStart_1842773 : Nat := 118140960795 + 1842773 * 2 ^ 59
def prefixEnd_1842773 : Nat := 4983230072969 + 3 ^ 40 * 1842773 * 2
def baseEnd_1842773 : Nat := 946228286127823875862747

theorem tailTrace_1842773 : CollatzResearch.WordTrace tailWord_1842773 prefixEnd_1842773 946228286127823875862747 := by
  unfold tailWord_1842773
  simp only [CollatzResearch.WordTrace]
  refine ⟨67211452952955616417324973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44807635301970410944883315 67211452952955616417324973)
  ·
    refine ⟨25204294857358356156496865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67211452952955616417324973 25204294857358356156496865)
    ·
      refine ⟨18903221143018767117372649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25204294857358356156496865 18903221143018767117372649)
      ·
        refine ⟨14177415857264075338029487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18903221143018767117372649 14177415857264075338029487)
        ·
          refine ⟨21266123785896113007044231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14177415857264075338029487 21266123785896113007044231)
          ·
            refine ⟨31899185678844169510566347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21266123785896113007044231 31899185678844169510566347)
            ·
              refine ⟨47848778518266254265849521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31899185678844169510566347 47848778518266254265849521)
              ·
                refine ⟨35886583888699690699387141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47848778518266254265849521 35886583888699690699387141)
                ·
                  refine ⟨6728734479131192006135089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35886583888699690699387141 6728734479131192006135089)
                  ·
                    refine ⟨5046550859348394004601317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6728734479131192006135089 5046550859348394004601317)
                    ·
                      refine ⟨946228286127823875862747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5046550859348394004601317 946228286127823875862747)
                      ·
                        rfl

theorem cell23_1842773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_1842773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1842773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1842773 prefixEnd_1842773 := by exact prefixLift 1842773
  have htrace : WordTrace (prefixWord ++ tailWord_1842773) baseStart_1842773 baseEnd_1842773 := by
    simpa [prefixWord, tailWord_1842773, baseEnd_1842773] using wordTrace_append hprefix tailTrace_1842773
  have hstable : (prefixWord ++ tailWord_1842773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842773).length < 2 ^ (prefixWord ++ tailWord_1842773).sum := by decide
  have hdescent : baseEnd_1842773 < baseStart_1842773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842780 : List Nat := [2, 2, 4, 1, 2, 1, 2, 1, 2, 1, 5]
def baseStart_1842780 : Nat := 118140960795 + 1842780 * 2 ^ 59
def prefixEnd_1842780 : Nat := 4983230072969 + 3 ^ 40 * 1842780 * 2
def baseEnd_1842780 : Nat := 946231880492405348475215

theorem tailTrace_1842780 : CollatzResearch.WordTrace tailWord_1842780 prefixEnd_1842780 946231880492405348475215 := by
  unfold tailWord_1842780
  simp only [CollatzResearch.WordTrace]
  refine ⟨33605854131965128306414897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44807805509286837741886529 33605854131965128306414897)
  ·
    refine ⟨25204390598973846229811173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33605854131965128306414897 25204390598973846229811173)
    ·
      refine ⟨4725823237307596168089595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25204390598973846229811173 4725823237307596168089595)
      ·
        refine ⟨7088734855961394252134393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4725823237307596168089595 7088734855961394252134393)
        ·
          refine ⟨5316551141971045689100795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7088734855961394252134393 5316551141971045689100795)
          ·
            refine ⟨7974826712956568533651193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5316551141971045689100795 7974826712956568533651193)
            ·
              refine ⟨5981120034717426400238395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7974826712956568533651193 5981120034717426400238395)
              ·
                refine ⟨8971680052076139600357593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5981120034717426400238395 8971680052076139600357593)
                ·
                  refine ⟨6728760039057104700268195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8971680052076139600357593 6728760039057104700268195)
                  ·
                    refine ⟨10093140058585657050402293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6728760039057104700268195 10093140058585657050402293)
                    ·
                      refine ⟨946231880492405348475215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10093140058585657050402293 946231880492405348475215)
                      ·
                        rfl

theorem cell23_1842780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_1842780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1842780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1842780 prefixEnd_1842780 := by exact prefixLift 1842780
  have htrace : WordTrace (prefixWord ++ tailWord_1842780) baseStart_1842780 baseEnd_1842780 := by
    simpa [prefixWord, tailWord_1842780, baseEnd_1842780] using wordTrace_append hprefix tailTrace_1842780
  have hstable : (prefixWord ++ tailWord_1842780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842780).length < 2 ^ (prefixWord ++ tailWord_1842780).sum := by decide
  have hdescent : baseEnd_1842780 < baseStart_1842780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842794 : List Nat := [3, 1, 3, 2, 1, 2, 1, 4, 2, 2, 2]
def baseStart_1842794 : Nat := 118140960795 + 1842794 * 2 ^ 59
def prefixEnd_1842794 : Nat := 4983230072969 + 3 ^ 40 * 1842794 * 2
def baseEnd_1842794 : Nat := 946239069221568293700151

theorem tailTrace_1842794 : CollatzResearch.WordTrace tailWord_1842794 prefixEnd_1842794 946239069221568293700151 := by
  unfold tailWord_1842794
  simp only [CollatzResearch.WordTrace]
  refine ⟨16803054721469884250959859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44808145923919691335892957 16803054721469884250959859)
  ·
    refine ⟨25204582082204826376439789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16803054721469884250959859 25204582082204826376439789)
    ·
      refine ⟨9451718280826809891164921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25204582082204826376439789 9451718280826809891164921)
      ·
        refine ⟨7088788710620107418373691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9451718280826809891164921 7088788710620107418373691)
        ·
          refine ⟨10633183065930161127560537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7088788710620107418373691 10633183065930161127560537)
          ·
            refine ⟨7974887299447620845670403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10633183065930161127560537 7974887299447620845670403)
            ·
              refine ⟨11962330949171431268505605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7974887299447620845670403 11962330949171431268505605)
              ·
                refine ⟨2242937052969643362844801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11962330949171431268505605 2242937052969643362844801)
                ·
                  refine ⟨1682202789727232522133601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2242937052969643362844801 1682202789727232522133601)
                  ·
                    refine ⟨1261652092295424391600201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1682202789727232522133601 1261652092295424391600201)
                    ·
                      refine ⟨946239069221568293700151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1261652092295424391600201 946239069221568293700151)
                      ·
                        rfl

theorem cell23_1842794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_1842794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1842794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1842794 prefixEnd_1842794 := by exact prefixLift 1842794
  have htrace : WordTrace (prefixWord ++ tailWord_1842794) baseStart_1842794 baseEnd_1842794 := by
    simpa [prefixWord, tailWord_1842794, baseEnd_1842794] using wordTrace_append hprefix tailTrace_1842794
  have hstable : (prefixWord ++ tailWord_1842794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842794).length < 2 ^ (prefixWord ++ tailWord_1842794).sum := by decide
  have hdescent : baseEnd_1842794 < baseStart_1842794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842830 : List Nat := [4, 1, 1, 3, 1, 3, 1, 1, 1, 7]
def baseStart_1842830 : Nat := 118140960795 + 1842830 * 2 ^ 59
def prefixEnd_1842830 : Nat := 4983230072969 + 3 ^ 40 * 1842830 * 2
def baseEnd_1842830 : Nat := 315419184841710050949995

theorem tailTrace_1842830 : CollatzResearch.WordTrace tailWord_1842830 prefixEnd_1842830 315419184841710050949995 := by
  unfold tailWord_1842830
  simp only [CollatzResearch.WordTrace]
  refine ⟨8401691489218639394018743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44809021275832743434766629 8401691489218639394018743)
  ·
    refine ⟨12602537233827959091028115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8401691489218639394018743 12602537233827959091028115)
    ·
      refine ⟨18903805850741938636542173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12602537233827959091028115 18903805850741938636542173)
      ·
        refine ⟨7088927194028226988703315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18903805850741938636542173 7088927194028226988703315)
        ·
          refine ⟨10633390791042340483054973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7088927194028226988703315 10633390791042340483054973)
          ·
            refine ⟨3987521546640877681145615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10633390791042340483054973 3987521546640877681145615)
            ·
              refine ⟨5981282319961316521718423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3987521546640877681145615 5981282319961316521718423)
              ·
                refine ⟨8971923479941974782577635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5981282319961316521718423 8971923479941974782577635)
                ·
                  refine ⟨13457885219912962173866453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8971923479941974782577635 13457885219912962173866453)
                  ·
                    refine ⟨315419184841710050949995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13457885219912962173866453 315419184841710050949995)
                    ·
                      rfl

theorem cell23_1842830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 1, 7].length) (baseStart_1842830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1842830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1842830 prefixEnd_1842830 := by exact prefixLift 1842830
  have htrace : WordTrace (prefixWord ++ tailWord_1842830) baseStart_1842830 baseEnd_1842830 := by
    simpa [prefixWord, tailWord_1842830, baseEnd_1842830] using wordTrace_append hprefix tailTrace_1842830
  have hstable : (prefixWord ++ tailWord_1842830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842830).length < 2 ^ (prefixWord ++ tailWord_1842830).sum := by decide
  have hdescent : baseEnd_1842830 < baseStart_1842830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842834 : List Nat := [3, 2, 3, 1, 3, 1, 2, 3, 5]
def baseStart_1842834 : Nat := 118140960795 + 1842834 * 2 ^ 59
def prefixEnd_1842834 : Nat := 4983230072969 + 3 ^ 40 * 1842834 * 2
def baseEnd_1842834 : Nat := 105139956494194237466663

theorem tailTrace_1842834 : CollatzResearch.WordTrace tailWord_1842834 prefixEnd_1842834 105139956494194237466663 := by
  unfold tailWord_1842834
  simp only [CollatzResearch.WordTrace]
  refine ⟨16803419451433655958823889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44809118537156415890197037 16803419451433655958823889)
  ·
    refine ⟨12602564588575241969117917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16803419451433655958823889 12602564588575241969117917)
    ·
      refine ⟨4725961720715715738419219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12602564588575241969117917 4725961720715715738419219)
      ·
        refine ⟨7088942581073573607628829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4725961720715715738419219 7088942581073573607628829)
        ·
          refine ⟨2658353467902590102860811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7088942581073573607628829 2658353467902590102860811)
          ·
            refine ⟨3987530201853885154291217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2658353467902590102860811 3987530201853885154291217)
            ·
              refine ⟨2990647651390413865718413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3987530201853885154291217 2990647651390413865718413)
              ·
                refine ⟨1121492869271405199644405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2990647651390413865718413 1121492869271405199644405)
                ·
                  refine ⟨105139956494194237466663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1121492869271405199644405 105139956494194237466663)
                  ·
                    rfl

theorem cell23_1842834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 3, 5].length) (baseStart_1842834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1842834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1842834 prefixEnd_1842834 := by exact prefixLift 1842834
  have htrace : WordTrace (prefixWord ++ tailWord_1842834) baseStart_1842834 baseEnd_1842834 := by
    simpa [prefixWord, tailWord_1842834, baseEnd_1842834] using wordTrace_append hprefix tailTrace_1842834
  have hstable : (prefixWord ++ tailWord_1842834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842834).length < 2 ^ (prefixWord ++ tailWord_1842834).sum := by decide
  have hdescent : baseEnd_1842834 < baseStart_1842834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842853 : List Nat := [1, 3, 1, 2, 1, 2, 2, 1, 2, 3, 5]
def baseStart_1842853 : Nat := 118140960795 + 1842853 * 2 ^ 59
def prefixEnd_1842853 : Nat := 4983230072969 + 3 ^ 40 * 1842853 * 2
def baseEnd_1842853 : Nat := 946269364580183562862379

theorem tailTrace_1842853 : CollatzResearch.WordTrace tailWord_1842853 prefixEnd_1842853 946269364580183562862379 := by
  unfold tailWord_1842853
  simp only [CollatzResearch.WordTrace]
  refine ⟨67214370792665790080237213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44809580528443860053491475 67214370792665790080237213)
  ·
    refine ⟨25205389047249671280088955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67214370792665790080237213 25205389047249671280088955)
    ·
      refine ⟨37808083570874506920133433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25205389047249671280088955 37808083570874506920133433)
      ·
        refine ⟨28356062678155880190100075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37808083570874506920133433 28356062678155880190100075)
        ·
          refine ⟨42534094017233820285150113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28356062678155880190100075 42534094017233820285150113)
          ·
            refine ⟨31900570512925365213862585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42534094017233820285150113 31900570512925365213862585)
            ·
              refine ⟨23925427884694023910396939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31900570512925365213862585 23925427884694023910396939)
              ·
                refine ⟨35888141827041035865595409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23925427884694023910396939 35888141827041035865595409)
                ·
                  refine ⟨26916106370280776899196557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35888141827041035865595409 26916106370280776899196557)
                  ·
                    refine ⟨10093539888855291337198709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26916106370280776899196557 10093539888855291337198709)
                    ·
                      refine ⟨946269364580183562862379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10093539888855291337198709 946269364580183562862379)
                      ·
                        rfl

theorem cell23_1842853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_1842853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1842853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1842853 prefixEnd_1842853 := by exact prefixLift 1842853
  have htrace : WordTrace (prefixWord ++ tailWord_1842853) baseStart_1842853 baseEnd_1842853 := by
    simpa [prefixWord, tailWord_1842853, baseEnd_1842853] using wordTrace_append hprefix tailTrace_1842853
  have hstable : (prefixWord ++ tailWord_1842853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842853).length < 2 ^ (prefixWord ++ tailWord_1842853).sum := by decide
  have hdescent : baseEnd_1842853 < baseStart_1842853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842863 : List Nat := [1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 6]
def baseStart_1842863 : Nat := 118140960795 + 1842863 * 2 ^ 59
def prefixEnd_1842863 : Nat := 4983230072969 + 3 ^ 40 * 1842863 * 2
def baseEnd_1842863 : Nat := 946274499386728523737333

theorem tailTrace_1842863 : CollatzResearch.WordTrace tailWord_1842863 prefixEnd_1842863 946274499386728523737333 := by
  unfold tailWord_1842863
  simp only [CollatzResearch.WordTrace]
  refine ⟨67214735522629561788101243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44809823681753041192067495 67214735522629561788101243)
  ·
    refine ⟨100822103283944342682151865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67214735522629561788101243 100822103283944342682151865)
    ·
      refine ⟨75616577462958257011613899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100822103283944342682151865 75616577462958257011613899)
      ·
        refine ⟨113424866194437385517420849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75616577462958257011613899 113424866194437385517420849)
        ·
          refine ⟨85068649645828039138065637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113424866194437385517420849 85068649645828039138065637)
          ·
            refine ⟨15950371808592757338387307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85068649645828039138065637 15950371808592757338387307)
            ·
              refine ⟨23925557712889136007580961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15950371808592757338387307 23925557712889136007580961)
              ·
                refine ⟨17944168284666852005685721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23925557712889136007580961 17944168284666852005685721)
                ·
                  refine ⟨13458126213500139004264291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17944168284666852005685721 13458126213500139004264291)
                  ·
                    refine ⟨20187189320250208506396437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13458126213500139004264291 20187189320250208506396437)
                    ·
                      refine ⟨946274499386728523737333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20187189320250208506396437 946274499386728523737333)
                      ·
                        rfl

theorem cell23_1842863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 6].length) (baseStart_1842863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1842863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1842863 prefixEnd_1842863 := by exact prefixLift 1842863
  have htrace : WordTrace (prefixWord ++ tailWord_1842863) baseStart_1842863 baseEnd_1842863 := by
    simpa [prefixWord, tailWord_1842863, baseEnd_1842863] using wordTrace_append hprefix tailTrace_1842863
  have hstable : (prefixWord ++ tailWord_1842863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842863).length < 2 ^ (prefixWord ++ tailWord_1842863).sum := by decide
  have hdescent : baseEnd_1842863 < baseStart_1842863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842927 : List Nat := [1, 1, 2, 1, 5, 1, 1, 2, 4, 3, 2]
def baseStart_1842927 : Nat := 118140960795 + 1842927 * 2 ^ 59
def prefixEnd_1842927 : Nat := 4983230072969 + 3 ^ 40 * 1842927 * 2
def baseEnd_1842927 : Nat := 946307362148616273337039

theorem tailTrace_1842927 : CollatzResearch.WordTrace tailWord_1842927 prefixEnd_1842927 946307362148616273337039 := by
  unfold tailWord_1842927
  simp only [CollatzResearch.WordTrace]
  refine ⟨67217069794397700718431035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44811379862931800478954023 67217069794397700718431035)
  ·
    refine ⟨100825604691596551077646553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67217069794397700718431035 100825604691596551077646553)
    ·
      refine ⟨75619203518697413308234915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100825604691596551077646553 75619203518697413308234915)
      ·
        refine ⟨113428805278046119962352373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75619203518697413308234915 113428805278046119962352373)
        ·
          refine ⟨10633950494816823746470535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 113428805278046119962352373 10633950494816823746470535)
          ·
            refine ⟨15950925742225235619705803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10633950494816823746470535 15950925742225235619705803)
            ·
              refine ⟨23926388613337853429558705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15950925742225235619705803 23926388613337853429558705)
              ·
                refine ⟨17944791460003390072169029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23926388613337853429558705 17944791460003390072169029)
                ·
                  refine ⟨3364648398750635638531693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17944791460003390072169029 3364648398750635638531693)
                  ·
                    refine ⟨1261743149531488364449385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3364648398750635638531693 1261743149531488364449385)
                    ·
                      refine ⟨946307362148616273337039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1261743149531488364449385 946307362148616273337039)
                      ·
                        rfl

theorem cell23_1842927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 4, 3, 2].length) (baseStart_1842927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1842927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1842927 prefixEnd_1842927 := by exact prefixLift 1842927
  have htrace : WordTrace (prefixWord ++ tailWord_1842927) baseStart_1842927 baseEnd_1842927 := by
    simpa [prefixWord, tailWord_1842927, baseEnd_1842927] using wordTrace_append hprefix tailTrace_1842927
  have hstable : (prefixWord ++ tailWord_1842927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842927).length < 2 ^ (prefixWord ++ tailWord_1842927).sum := by decide
  have hdescent : baseEnd_1842927 < baseStart_1842927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842954 : List Nat := [3, 1, 2, 2, 1, 4, 3, 1, 1, 5]
def baseStart_1842954 : Nat := 118140960795 + 1842954 * 2 ^ 59
def prefixEnd_1842954 : Nat := 4983230072969 + 3 ^ 40 * 1842954 * 2
def baseEnd_1842954 : Nat := 315440408708762555899805

theorem tailTrace_1842954 : CollatzResearch.WordTrace tailWord_1842954 prefixEnd_1842954 315440408708762555899805 := by
  unfold tailWord_1842954
  simp only [CollatzResearch.WordTrace]
  refine ⟨16804513641324971082415979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44812036376866589553109277 16804513641324971082415979)
  ·
    refine ⟨25206770461987456623623969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16804513641324971082415979 25206770461987456623623969)
    ·
      refine ⟨18905077846490592467717977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25206770461987456623623969 18905077846490592467717977)
      ·
        refine ⟨14178808384867944350788483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18905077846490592467717977 14178808384867944350788483)
        ·
          refine ⟨21268212577301916526182725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14178808384867944350788483 21268212577301916526182725)
          ·
            refine ⟨3987789858244109348659261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21268212577301916526182725 3987789858244109348659261)
            ·
              refine ⟨1495421196841541005747223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3987789858244109348659261 1495421196841541005747223)
              ·
                refine ⟨2243131795262311508620835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1495421196841541005747223 2243131795262311508620835)
                ·
                  refine ⟨3364697692893467262931253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2243131795262311508620835 3364697692893467262931253)
                  ·
                    refine ⟨315440408708762555899805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3364697692893467262931253 315440408708762555899805)
                    ·
                      rfl

theorem cell23_1842954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 1, 1, 5].length) (baseStart_1842954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1842954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1842954 prefixEnd_1842954 := by exact prefixLift 1842954
  have htrace : WordTrace (prefixWord ++ tailWord_1842954) baseStart_1842954 baseEnd_1842954 := by
    simpa [prefixWord, tailWord_1842954, baseEnd_1842954] using wordTrace_append hprefix tailTrace_1842954
  have hstable : (prefixWord ++ tailWord_1842954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842954).length < 2 ^ (prefixWord ++ tailWord_1842954).sum := by decide
  have hdescent : baseEnd_1842954 < baseStart_1842954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842977 : List Nat := [1, 2, 3, 2, 1, 3, 1, 2, 3, 2, 3]
def baseStart_1842977 : Nat := 118140960795 + 1842977 * 2 ^ 59
def prefixEnd_1842977 : Nat := 4983230072969 + 3 ^ 40 * 1842977 * 2
def baseEnd_1842977 : Nat := 946333036181341077711809

theorem tailTrace_1842977 : CollatzResearch.WordTrace tailWord_1842977 prefixEnd_1842977 946333036181341077711809 := by
  unfold tailWord_1842977
  simp only [CollatzResearch.WordTrace]
  refine ⟨67218893444216559257751185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44812595629477706171834123 67218893444216559257751185)
  ·
    refine ⟨50414170083162419443313389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67218893444216559257751185 50414170083162419443313389)
    ·
      refine ⟨18905313781185907291242521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50414170083162419443313389 18905313781185907291242521)
      ·
        refine ⟨14178985335889430468431891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18905313781185907291242521 14178985335889430468431891)
        ·
          refine ⟨21268478003834145702647837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14178985335889430468431891 21268478003834145702647837)
          ·
            refine ⟨7975679251437804638492939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21268478003834145702647837 7975679251437804638492939)
            ·
              refine ⟨11963518877156706957739409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7975679251437804638492939 11963518877156706957739409)
              ·
                refine ⟨8972639157867530218304557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11963518877156706957739409 8972639157867530218304557)
                ·
                  refine ⟨3364739684200323831864209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8972639157867530218304557 3364739684200323831864209)
                  ·
                    refine ⟨2523554763150242873898157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3364739684200323831864209 2523554763150242873898157)
                    ·
                      refine ⟨946333036181341077711809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2523554763150242873898157 946333036181341077711809)
                      ·
                        rfl

theorem cell23_1842977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_1842977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1842977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1842977 prefixEnd_1842977 := by exact prefixLift 1842977
  have htrace : WordTrace (prefixWord ++ tailWord_1842977) baseStart_1842977 baseEnd_1842977 := by
    simpa [prefixWord, tailWord_1842977, baseEnd_1842977] using wordTrace_append hprefix tailTrace_1842977
  have hstable : (prefixWord ++ tailWord_1842977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842977).length < 2 ^ (prefixWord ++ tailWord_1842977).sum := by decide
  have hdescent : baseEnd_1842977 < baseStart_1842977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842984 : List Nat := [2, 1, 5, 1, 1, 2, 2, 3, 2, 4]
def baseStart_1842984 : Nat := 118140960795 + 1842984 * 2 ^ 59
def prefixEnd_1842984 : Nat := 4983230072969 + 3 ^ 40 * 1842984 * 2
def baseEnd_1842984 : Nat := 315445543515307516774759

theorem tailTrace_1842984 : CollatzResearch.WordTrace tailWord_1842984 prefixEnd_1842984 315445543515307516774759 := by
  unfold tailWord_1842984
  simp only [CollatzResearch.WordTrace]
  refine ⟨33609574377595599726628003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44812765836794132968837337 33609574377595599726628003)
  ·
    refine ⟨50414361566393399589942005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33609574377595599726628003 50414361566393399589942005)
    ·
      refine ⟨4726346396849381211557063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50414361566393399589942005 4726346396849381211557063)
      ·
        refine ⟨7089519595274071817335595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4726346396849381211557063 7089519595274071817335595)
        ·
          refine ⟨10634279392911107726003393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7089519595274071817335595 10634279392911107726003393)
          ·
            refine ⟨7975709544683330794502545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10634279392911107726003393 7975709544683330794502545)
            ·
              refine ⟨5981782158512498095876909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7975709544683330794502545 5981782158512498095876909)
              ·
                refine ⟨2243168309442186785953841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5981782158512498095876909 2243168309442186785953841)
                ·
                  refine ⟨1682376232081640089465381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2243168309442186785953841 1682376232081640089465381)
                  ·
                    refine ⟨315445543515307516774759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1682376232081640089465381 315445543515307516774759)
                    ·
                      rfl

theorem cell23_1842984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_1842984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1842984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1842984 prefixEnd_1842984 := by exact prefixLift 1842984
  have htrace : WordTrace (prefixWord ++ tailWord_1842984) baseStart_1842984 baseEnd_1842984 := by
    simpa [prefixWord, tailWord_1842984, baseEnd_1842984] using wordTrace_append hprefix tailTrace_1842984
  have hstable : (prefixWord ++ tailWord_1842984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842984).length < 2 ^ (prefixWord ++ tailWord_1842984).sum := by decide
  have hdescent : baseEnd_1842984 < baseStart_1842984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843011 : List Nat := [1, 1, 1, 3, 1, 7, 2, 1, 1, 2, 3]
def baseStart_1843011 : Nat := 118140960795 + 1843011 * 2 ^ 59
def prefixEnd_1843011 : Nat := 4983230072969 + 3 ^ 40 * 1843011 * 2
def baseEnd_1843011 : Nat := 946350494523593944686653

theorem tailTrace_1843011 : CollatzResearch.WordTrace tailWord_1843011 prefixEnd_1843011 946350494523593944686653 := by
  unfold tailWord_1843011
  simp only [CollatzResearch.WordTrace]
  refine ⟨67220133526093383064488887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44813422350728922042992591 67220133526093383064488887)
  ·
    refine ⟨100830200289140074596733331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67220133526093383064488887 100830200289140074596733331)
    ·
      refine ⟨151245300433710111895099997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100830200289140074596733331 151245300433710111895099997)
      ·
        refine ⟨56716987662641291960662499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151245300433710111895099997 56716987662641291960662499)
        ·
          refine ⟨85075481493961937940993749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56716987662641291960662499 85075481493961937940993749)
          ·
            refine ⟨1993956597514732920492041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 85075481493961937940993749 1993956597514732920492041)
            ·
              refine ⟨1495467448136049690369031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1993956597514732920492041 1495467448136049690369031)
              ·
                refine ⟨2243201172204074535553547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1495467448136049690369031 2243201172204074535553547)
                ·
                  refine ⟨3364801758306111803330321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2243201172204074535553547 3364801758306111803330321)
                  ·
                    refine ⟨2523601318729583852497741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3364801758306111803330321 2523601318729583852497741)
                    ·
                      refine ⟨946350494523593944686653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2523601318729583852497741 946350494523593944686653)
                      ·
                        rfl

theorem cell23_1843011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 1, 1, 2, 3].length) (baseStart_1843011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1843011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1843011 prefixEnd_1843011 := by exact prefixLift 1843011
  have htrace : WordTrace (prefixWord ++ tailWord_1843011) baseStart_1843011 baseEnd_1843011 := by
    simpa [prefixWord, tailWord_1843011, baseEnd_1843011] using wordTrace_append hprefix tailTrace_1843011
  have hstable : (prefixWord ++ tailWord_1843011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843011).length < 2 ^ (prefixWord ++ tailWord_1843011).sum := by decide
  have hdescent : baseEnd_1843011 < baseStart_1843011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843014 : List Nat := [6, 1, 1, 2, 1, 2, 10]
def baseStart_1843014 : Nat := 118140960795 + 1843014 * 2 ^ 59
def prefixEnd_1843014 : Nat := 4983230072969 + 3 ^ 40 * 1843014 * 2
def baseEnd_1843014 : Nat := 11683358456364906579619

theorem tailTrace_1843014 : CollatzResearch.WordTrace tailWord_1843014 prefixEnd_1843014 11683358456364906579619 := by
  unfold tailWord_1843014
  simp only [CollatzResearch.WordTrace]
  refine ⟨2100632592033828580526503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 44813495296721676384565397 2100632592033828580526503)
  ·
    refine ⟨3150948888050742870789755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2100632592033828580526503 3150948888050742870789755)
    ·
      refine ⟨4726423332076114306184633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3150948888050742870789755 4726423332076114306184633)
      ·
        refine ⟨3544817499057085729638475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4726423332076114306184633 3544817499057085729638475)
        ·
          refine ⟨5317226248585628594457713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3544817499057085729638475 5317226248585628594457713)
          ·
            refine ⟨3987919686439221445843285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5317226248585628594457713 3987919686439221445843285)
            ·
              refine ⟨11683358456364906579619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3987919686439221445843285 11683358456364906579619)
              ·
                rfl

theorem cell23_1843014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 10].length) (baseStart_1843014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1843014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1843014 prefixEnd_1843014 := by exact prefixLift 1843014
  have htrace : WordTrace (prefixWord ++ tailWord_1843014) baseStart_1843014 baseEnd_1843014 := by
    simpa [prefixWord, tailWord_1843014, baseEnd_1843014] using wordTrace_append hprefix tailTrace_1843014
  have hstable : (prefixWord ++ tailWord_1843014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843014).length < 2 ^ (prefixWord ++ tailWord_1843014).sum := by decide
  have hdescent : baseEnd_1843014 < baseStart_1843014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843041 : List Nat := [1, 2, 3, 1, 1, 1, 7, 1, 2, 1, 3]
def baseStart_1843041 : Nat := 118140960795 + 1843041 * 2 ^ 59
def prefixEnd_1843041 : Nat := 4983230072969 + 3 ^ 40 * 1843041 * 2
def baseEnd_1843041 : Nat := 946365898943228827311515

theorem tailTrace_1843041 : CollatzResearch.WordTrace tailWord_1843041 prefixEnd_1843041 946365898943228827311515 := by
  unfold tailWord_1843041
  simp only [CollatzResearch.WordTrace]
  refine ⟨67221227715984698188080977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44814151810656465458720651 67221227715984698188080977)
  ·
    refine ⟨50415920786988523641060733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67221227715984698188080977 50415920786988523641060733)
    ·
      refine ⟨18905970295120696365397775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50415920786988523641060733 18905970295120696365397775)
      ·
        refine ⟨28358955442681044548096663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18905970295120696365397775 28358955442681044548096663)
        ·
          refine ⟨42538433164021566822144995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28358955442681044548096663 42538433164021566822144995)
          ·
            refine ⟨63807649746032350233217493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42538433164021566822144995 63807649746032350233217493)
            ·
              refine ⟨1495491790922633208591035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 63807649746032350233217493 1495491790922633208591035)
              ·
                refine ⟨2243237686383949812886553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1495491790922633208591035 2243237686383949812886553)
                ·
                  refine ⟨1682428264787962359664915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2243237686383949812886553 1682428264787962359664915)
                  ·
                    refine ⟨2523642397181943539497373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1682428264787962359664915 2523642397181943539497373)
                    ·
                      refine ⟨946365898943228827311515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2523642397181943539497373 946365898943228827311515)
                      ·
                        rfl

theorem cell23_1843041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 1, 2, 1, 3].length) (baseStart_1843041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1843041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1843041 prefixEnd_1843041 := by exact prefixLift 1843041
  have htrace : WordTrace (prefixWord ++ tailWord_1843041) baseStart_1843041 baseEnd_1843041 := by
    simpa [prefixWord, tailWord_1843041, baseEnd_1843041] using wordTrace_append hprefix tailTrace_1843041
  have hstable : (prefixWord ++ tailWord_1843041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843041).length < 2 ^ (prefixWord ++ tailWord_1843041).sum := by decide
  have hdescent : baseEnd_1843041 < baseStart_1843041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843081 : List Nat := [1, 2, 1, 1, 5, 1, 2, 4, 2, 2, 2]
def baseStart_1843081 : Nat := 118140960795 + 1843081 * 2 ^ 59
def prefixEnd_1843081 : Nat := 4983230072969 + 3 ^ 40 * 1843081 * 2
def baseEnd_1843081 : Nat := 946386438169408670811331

theorem tailTrace_1843081 : CollatzResearch.WordTrace tailWord_1843081 prefixEnd_1843081 946386438169408670811331 := by
  unfold tailWord_1843081
  simp only [CollatzResearch.WordTrace]
  refine ⟨67222686635839785019537097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44815124423893190013024731 67222686635839785019537097)
  ·
    refine ⟨50417014976879838764652823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67222686635839785019537097 50417014976879838764652823)
    ·
      refine ⟨75625522465319758146979235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50417014976879838764652823 75625522465319758146979235)
      ·
        refine ⟨113438283697979637220468853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75625522465319758146979235 113438283697979637220468853)
        ·
          refine ⟨10634839096685590989418955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 113438283697979637220468853 10634839096685590989418955)
          ·
            refine ⟨15952258645028386484128433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10634839096685590989418955 15952258645028386484128433)
            ·
              refine ⟨11964193983771289863096325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15952258645028386484128433 11964193983771289863096325)
              ·
                refine ⟨2243286371957116849330561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11964193983771289863096325 2243286371957116849330561)
                ·
                  refine ⟨1682464778967837636997921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2243286371957116849330561 1682464778967837636997921)
                  ·
                    refine ⟨1261848584225878227748441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1682464778967837636997921 1261848584225878227748441)
                    ·
                      refine ⟨946386438169408670811331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1261848584225878227748441 946386438169408670811331)
                      ·
                        rfl

theorem cell23_1843081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 4, 2, 2, 2].length) (baseStart_1843081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1843081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1843081 prefixEnd_1843081 := by exact prefixLift 1843081
  have htrace : WordTrace (prefixWord ++ tailWord_1843081) baseStart_1843081 baseEnd_1843081 := by
    simpa [prefixWord, tailWord_1843081, baseEnd_1843081] using wordTrace_append hprefix tailTrace_1843081
  have hstable : (prefixWord ++ tailWord_1843081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843081).length < 2 ^ (prefixWord ++ tailWord_1843081).sum := by decide
  have hdescent : baseEnd_1843081 < baseStart_1843081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843097 : List Nat := [1, 2, 1, 2, 1, 3, 2, 3, 2, 3, 3]
def baseStart_1843097 : Nat := 118140960795 + 1843097 * 2 ^ 59
def prefixEnd_1843097 : Nat := 4983230072969 + 3 ^ 40 * 1843097 * 2
def baseEnd_1843097 : Nat := 946394653859880608211257

theorem tailTrace_1843097 : CollatzResearch.WordTrace tailWord_1843097 prefixEnd_1843097 946394653859880608211257 := by
  unfold tailWord_1843097
  simp only [CollatzResearch.WordTrace]
  refine ⟨67223270203781819752119545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44815513469187879834746363 67223270203781819752119545)
  ·
    refine ⟨50417452652836364814089659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67223270203781819752119545 50417452652836364814089659)
    ·
      refine ⟨75626178979254547221134489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50417452652836364814089659 75626178979254547221134489)
      ·
        refine ⟨56719634234440910415850867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75626178979254547221134489 56719634234440910415850867)
        ·
          refine ⟨85079451351661365623776301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56719634234440910415850867 85079451351661365623776301)
          ·
            refine ⟨31904794256873012108916113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85079451351661365623776301 31904794256873012108916113)
            ·
              refine ⟨23928595692654759081687085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31904794256873012108916113 23928595692654759081687085)
              ·
                refine ⟨8973223384745534655632657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23928595692654759081687085 8973223384745534655632657)
                ·
                  refine ⟨6729917538559150991724493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8973223384745534655632657 6729917538559150991724493)
                  ·
                    refine ⟨2523719076959681621896685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6729917538559150991724493 2523719076959681621896685)
                    ·
                      refine ⟨946394653859880608211257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2523719076959681621896685 946394653859880608211257)
                      ·
                        rfl

theorem cell23_1843097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2, 3, 3].length) (baseStart_1843097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1843097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1843097 prefixEnd_1843097 := by exact prefixLift 1843097
  have htrace : WordTrace (prefixWord ++ tailWord_1843097) baseStart_1843097 baseEnd_1843097 := by
    simpa [prefixWord, tailWord_1843097, baseEnd_1843097] using wordTrace_append hprefix tailTrace_1843097
  have hstable : (prefixWord ++ tailWord_1843097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843097).length < 2 ^ (prefixWord ++ tailWord_1843097).sum := by decide
  have hdescent : baseEnd_1843097 < baseStart_1843097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843098 : List Nat := [3, 1, 1, 4, 2, 2, 1, 3, 2, 2, 2]
def baseStart_1843098 : Nat := 118140960795 + 1843098 * 2 ^ 59
def prefixEnd_1843098 : Nat := 4983230072969 + 3 ^ 40 * 1843098 * 2
def baseEnd_1843098 : Nat := 946395167340535104298753

theorem tailTrace_1843098 : CollatzResearch.WordTrace tailWord_1843098 prefixEnd_1843098 946395167340535104298753 := by
  unfold tailWord_1843098
  simp only [CollatzResearch.WordTrace]
  refine ⟨16805826669194549230726487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44815537784518797948603965 16805826669194549230726487)
  ·
    refine ⟨25208740003791823846089731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16805826669194549230726487 25208740003791823846089731)
    ·
      refine ⟨37813110005687735769134597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25208740003791823846089731 37813110005687735769134597)
      ·
        refine ⟨7089958126066450456712737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37813110005687735769134597 7089958126066450456712737)
        ·
          refine ⟨5317468594549837842534553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7089958126066450456712737 5317468594549837842534553)
          ·
            refine ⟨3988101445912378381900915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5317468594549837842534553 3988101445912378381900915)
            ·
              refine ⟨5982152168868567572851373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3988101445912378381900915 5982152168868567572851373)
              ·
                refine ⟨2243307063325712839819265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5982152168868567572851373 2243307063325712839819265)
                ·
                  refine ⟨1682480297494284629864449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2243307063325712839819265 1682480297494284629864449)
                  ·
                    refine ⟨1261860223120713472398337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1682480297494284629864449 1261860223120713472398337)
                    ·
                      refine ⟨946395167340535104298753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1261860223120713472398337 946395167340535104298753)
                      ·
                        rfl

theorem cell23_1843098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_1843098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1843098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1843098 prefixEnd_1843098 := by exact prefixLift 1843098
  have htrace : WordTrace (prefixWord ++ tailWord_1843098) baseStart_1843098 baseEnd_1843098 := by
    simpa [prefixWord, tailWord_1843098, baseEnd_1843098] using wordTrace_append hprefix tailTrace_1843098
  have hstable : (prefixWord ++ tailWord_1843098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843098).length < 2 ^ (prefixWord ++ tailWord_1843098).sum := by decide
  have hdescent : baseEnd_1843098 < baseStart_1843098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843102 : List Nat := [4, 3, 1, 3, 1, 2, 1, 2, 1, 3, 2]
def baseStart_1843102 : Nat := 118140960795 + 1843102 * 2 ^ 59
def prefixEnd_1843102 : Nat := 4983230072969 + 3 ^ 40 * 1843102 * 2
def baseEnd_1843102 : Nat := 946397221263153088648735

theorem tailTrace_1843102 : CollatzResearch.WordTrace tailWord_1843102 prefixEnd_1843102 946397221263153088648735 := by
  unfold tailWord_1843102
  simp only [CollatzResearch.WordTrace]
  refine ⟨8402931571095463200756445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44815635045842470404034373 8402931571095463200756445)
  ·
    refine ⟨3151099339160798700283667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8402931571095463200756445 3151099339160798700283667)
    ·
      refine ⟨4726649008741198050425501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3151099339160798700283667 4726649008741198050425501)
      ·
        refine ⟨1772493378277949268909563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4726649008741198050425501 1772493378277949268909563)
        ·
          refine ⟨2658740067416923903364345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1772493378277949268909563 2658740067416923903364345)
          ·
            refine ⟨1994055050562692927523259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2658740067416923903364345 1994055050562692927523259)
            ·
              refine ⟨2991082575844039391284889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1994055050562692927523259 2991082575844039391284889)
              ·
                refine ⟨2243311931883029543463667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2991082575844039391284889 2243311931883029543463667)
                ·
                  refine ⟨3364967897824544315195501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2243311931883029543463667 3364967897824544315195501)
                  ·
                    refine ⟨1261862961684204118198313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3364967897824544315195501 1261862961684204118198313)
                    ·
                      refine ⟨946397221263153088648735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1261862961684204118198313 946397221263153088648735)
                      ·
                        rfl

theorem cell23_1843102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_1843102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1843102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1843102 prefixEnd_1843102 := by exact prefixLift 1843102
  have htrace : WordTrace (prefixWord ++ tailWord_1843102) baseStart_1843102 baseEnd_1843102 := by
    simpa [prefixWord, tailWord_1843102, baseEnd_1843102] using wordTrace_append hprefix tailTrace_1843102
  have hstable : (prefixWord ++ tailWord_1843102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843102).length < 2 ^ (prefixWord ++ tailWord_1843102).sum := by decide
  have hdescent : baseEnd_1843102 < baseStart_1843102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843134 : List Nat := [4, 2, 1, 1, 1, 3, 2, 2, 2, 5]
def baseStart_1843134 : Nat := 118140960795 + 1843134 * 2 ^ 59
def prefixEnd_1843134 : Nat := 4983230072969 + 3 ^ 40 * 1843134 * 2
def baseEnd_1843134 : Nat := 315471217548032321149529

theorem tailTrace_1843134 : CollatzResearch.WordTrace tailWord_1843134 prefixEnd_1843134 315471217548032321149529 := by
  unfold tailWord_1843134
  simp only [CollatzResearch.WordTrace]
  refine ⟨8403077463080971883902057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44816413136431850047477637 8403077463080971883902057)
  ·
    refine ⟨6302308097310728912926543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8403077463080971883902057 6302308097310728912926543)
    ·
      refine ⟨9453462145966093369389815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6302308097310728912926543 9453462145966093369389815)
      ·
        refine ⟨14180193218949140054084723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9453462145966093369389815 14180193218949140054084723)
        ·
          refine ⟨21270289828423710081127085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14180193218949140054084723 21270289828423710081127085)
          ·
            refine ⟨7976358685658891280422657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21270289828423710081127085 7976358685658891280422657)
            ·
              refine ⟨5982269014244168460316993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7976358685658891280422657 5982269014244168460316993)
              ·
                refine ⟨4486701760683126345237745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5982269014244168460316993 4486701760683126345237745)
                ·
                  refine ⟨3365026320512344758928309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4486701760683126345237745 3365026320512344758928309)
                  ·
                    refine ⟨315471217548032321149529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3365026320512344758928309 315471217548032321149529)
                    ·
                      rfl

theorem cell23_1843134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_1843134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1843134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1843134 prefixEnd_1843134 := by exact prefixLift 1843134
  have htrace : WordTrace (prefixWord ++ tailWord_1843134) baseStart_1843134 baseEnd_1843134 := by
    simpa [prefixWord, tailWord_1843134, baseEnd_1843134] using wordTrace_append hprefix tailTrace_1843134
  have hstable : (prefixWord ++ tailWord_1843134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843134).length < 2 ^ (prefixWord ++ tailWord_1843134).sum := by decide
  have hdescent : baseEnd_1843134 < baseStart_1843134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843171 : List Nat := [1, 1, 1, 6, 1, 4, 1, 1, 2, 1, 4]
def baseStart_1843171 : Nat := 118140960795 + 1843171 * 2 ^ 59
def prefixEnd_1843171 : Nat := 4983230072969 + 3 ^ 40 * 1843171 * 2
def baseEnd_1843171 : Nat := 946432651428313318685917

theorem tailTrace_1843171 : CollatzResearch.WordTrace tailWord_1843171 prefixEnd_1843171 946432651428313318685917 := by
  unfold tailWord_1843171
  simp only [CollatzResearch.WordTrace]
  refine ⟨67225969205513730390313367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44817312803675820260208911 67225969205513730390313367)
  ·
    refine ⟨100838953808270595585470051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67225969205513730390313367 100838953808270595585470051)
    ·
      refine ⟨151258430712405893378205077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100838953808270595585470051 151258430712405893378205077)
      ·
        refine ⟨7090238939644026252103363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 151258430712405893378205077 7090238939644026252103363)
        ·
          refine ⟨10635358409466039378155045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7090238939644026252103363 10635358409466039378155045)
          ·
            refine ⟨1994129701774882383404071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10635358409466039378155045 1994129701774882383404071)
            ·
              refine ⟨2991194552662323575106107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1994129701774882383404071 2991194552662323575106107)
              ·
                refine ⟨4486791828993485362659161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2991194552662323575106107 4486791828993485362659161)
                ·
                  refine ⟨3365093871745114021994371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4486791828993485362659161 3365093871745114021994371)
                  ·
                    refine ⟨5047640807617671032991557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3365093871745114021994371 5047640807617671032991557)
                    ·
                      refine ⟨946432651428313318685917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5047640807617671032991557 946432651428313318685917)
                      ·
                        rfl

theorem cell23_1843171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_1843171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1843171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1843171 prefixEnd_1843171 := by exact prefixLift 1843171
  have htrace : WordTrace (prefixWord ++ tailWord_1843171) baseStart_1843171 baseEnd_1843171 := by
    simpa [prefixWord, tailWord_1843171, baseEnd_1843171] using wordTrace_append hprefix tailTrace_1843171
  have hstable : (prefixWord ++ tailWord_1843171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843171).length < 2 ^ (prefixWord ++ tailWord_1843171).sum := by decide
  have hdescent : baseEnd_1843171 < baseStart_1843171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843187 : List Nat := [1, 1, 1, 2, 2, 2, 1, 2, 1, 7, 3]
def baseStart_1843187 : Nat := 118140960795 + 1843187 * 2 ^ 59
def prefixEnd_1843187 : Nat := 4983230072969 + 3 ^ 40 * 1843187 * 2
def baseEnd_1843187 : Nat := 946440867118785256085843

theorem tailTrace_1843187 : CollatzResearch.WordTrace tailWord_1843187 prefixEnd_1843187 946440867118785256085843 := by
  unfold tailWord_1843187
  simp only [CollatzResearch.WordTrace]
  refine ⟨67226552773455765122895815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44817701848970510081930543 67226552773455765122895815)
  ·
    refine ⟨100839829160183647684343723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67226552773455765122895815 100839829160183647684343723)
    ·
      refine ⟨151259743740275471526515585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100839829160183647684343723 151259743740275471526515585)
      ·
        refine ⟨113444807805206603644886689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151259743740275471526515585 113444807805206603644886689)
        ·
          refine ⟨85083605853904952733665017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113444807805206603644886689 85083605853904952733665017)
          ·
            refine ⟨63812704390428714550248763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85083605853904952733665017 63812704390428714550248763)
            ·
              refine ⟨95719056585643071825373145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63812704390428714550248763 95719056585643071825373145)
              ·
                refine ⟨71789292439232303869029859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95719056585643071825373145 71789292439232303869029859)
                ·
                  refine ⟨107683938658848455803544789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71789292439232303869029859 107683938658848455803544789)
                  ·
                    refine ⟨2523842312316760682895581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 107683938658848455803544789 2523842312316760682895581)
                    ·
                      refine ⟨946440867118785256085843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2523842312316760682895581 946440867118785256085843)
                      ·
                        rfl

theorem cell23_1843187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 7, 3].length) (baseStart_1843187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1843187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1843187 prefixEnd_1843187 := by exact prefixLift 1843187
  have htrace : WordTrace (prefixWord ++ tailWord_1843187) baseStart_1843187 baseEnd_1843187 := by
    simpa [prefixWord, tailWord_1843187, baseEnd_1843187] using wordTrace_append hprefix tailTrace_1843187
  have hstable : (prefixWord ++ tailWord_1843187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843187).length < 2 ^ (prefixWord ++ tailWord_1843187).sum := by decide
  have hdescent : baseEnd_1843187 < baseStart_1843187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843197 : List Nat := [1, 4, 1, 1, 1, 2, 3, 1, 1, 2, 6]
def baseStart_1843197 : Nat := 118140960795 + 1843197 * 2 ^ 59
def prefixEnd_1843197 : Nat := 4983230072969 + 3 ^ 40 * 1843197 * 2
def baseEnd_1843197 : Nat := 946446001925330216960797

theorem tailTrace_1843197 : CollatzResearch.WordTrace tailWord_1843197 prefixEnd_1843197 946446001925330216960797 := by
  unfold tailWord_1843197
  simp only [CollatzResearch.WordTrace]
  refine ⟨67226917503419536830759845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44817945002279691220506563 67226917503419536830759845)
  ·
    refine ⟨12605047031891163155767471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67226917503419536830759845 12605047031891163155767471)
    ·
      refine ⟨18907570547836744733651207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12605047031891163155767471 18907570547836744733651207)
      ·
        refine ⟨28361355821755117100476811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18907570547836744733651207 28361355821755117100476811)
        ·
          refine ⟨42542033732632675650715217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28361355821755117100476811 42542033732632675650715217)
          ·
            refine ⟨31906525299474506738036413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42542033732632675650715217 31906525299474506738036413)
            ·
              refine ⟨11964946987302940026763655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31906525299474506738036413 11964946987302940026763655)
              ·
                refine ⟨17947420480954410040145483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11964946987302940026763655 17947420480954410040145483)
                ·
                  refine ⟨26921130721431615060218225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17947420480954410040145483 26921130721431615060218225)
                  ·
                    refine ⟨20190848041073711295163669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26921130721431615060218225 20190848041073711295163669)
                    ·
                      refine ⟨946446001925330216960797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20190848041073711295163669 946446001925330216960797)
                      ·
                        rfl

theorem cell23_1843197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_1843197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1843197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1843197 prefixEnd_1843197 := by exact prefixLift 1843197
  have htrace : WordTrace (prefixWord ++ tailWord_1843197) baseStart_1843197 baseEnd_1843197 := by
    simpa [prefixWord, tailWord_1843197, baseEnd_1843197] using wordTrace_append hprefix tailTrace_1843197
  have hstable : (prefixWord ++ tailWord_1843197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843197).length < 2 ^ (prefixWord ++ tailWord_1843197).sum := by decide
  have hdescent : baseEnd_1843197 < baseStart_1843197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843198 : List Nat := [4, 2, 2, 2, 1, 2, 2, 1, 3, 4]
def baseStart_1843198 : Nat := 118140960795 + 1843198 * 2 ^ 59
def prefixEnd_1843198 : Nat := 4983230072969 + 3 ^ 40 * 1843198 * 2
def baseEnd_1843198 : Nat := 315482171801994904349431

theorem tailTrace_1843198 : CollatzResearch.WordTrace tailWord_1843198 prefixEnd_1843198 315482171801994904349431 := by
  unfold tailWord_1843198
  simp only [CollatzResearch.WordTrace]
  refine ⟨8403369247051989250193281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44817969317610609334364165 8403369247051989250193281)
  ·
    refine ⟨6302526935288991937644961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8403369247051989250193281 6302526935288991937644961)
    ·
      refine ⟨4726895201466743953233721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6302526935288991937644961 4726895201466743953233721)
      ·
        refine ⟨3545171401100057964925291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4726895201466743953233721 3545171401100057964925291)
        ·
          refine ⟨5317757101650086947387937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3545171401100057964925291 5317757101650086947387937)
          ·
            refine ⟨3988317826237565210540953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5317757101650086947387937 3988317826237565210540953)
            ·
              refine ⟨2991238369678173907905715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3988317826237565210540953 2991238369678173907905715)
              ·
                refine ⟨4486857554517260861858573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2991238369678173907905715 4486857554517260861858573)
                ·
                  refine ⟨1682571582943972823196965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4486857554517260861858573 1682571582943972823196965)
                  ·
                    refine ⟨315482171801994904349431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1682571582943972823196965 315482171801994904349431)
                    ·
                      rfl

theorem cell23_1843198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_1843198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1843198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1843198 prefixEnd_1843198 := by exact prefixLift 1843198
  have htrace : WordTrace (prefixWord ++ tailWord_1843198) baseStart_1843198 baseEnd_1843198 := by
    simpa [prefixWord, tailWord_1843198, baseEnd_1843198] using wordTrace_append hprefix tailTrace_1843198
  have hstable : (prefixWord ++ tailWord_1843198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843198).length < 2 ^ (prefixWord ++ tailWord_1843198).sum := by decide
  have hdescent : baseEnd_1843198 < baseStart_1843198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843231 : List Nat := [1, 1, 2, 4, 1, 2, 2, 3, 2, 3, 2]
def baseStart_1843231 : Nat := 118140960795 + 1843231 * 2 ^ 59
def prefixEnd_1843231 : Nat := 4983230072969 + 3 ^ 40 * 1843231 * 2
def baseEnd_1843231 : Nat := 946463460267583083935641

theorem tailTrace_1843231 : CollatzResearch.WordTrace tailWord_1843231 prefixEnd_1843231 946463460267583083935641 := by
  unfold tailWord_1843231
  simp only [CollatzResearch.WordTrace]
  refine ⟨67228157585296360637497547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44818771723530907091665031 67228157585296360637497547)
  ·
    refine ⟨100842236377944540956246321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67228157585296360637497547 100842236377944540956246321)
    ·
      refine ⟨75631677283458405717184741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100842236377944540956246321 75631677283458405717184741)
      ·
        refine ⟨14180939490648451071972139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75631677283458405717184741 14180939490648451071972139)
        ·
          refine ⟨21271409235972676607958209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14180939490648451071972139 21271409235972676607958209)
          ·
            refine ⟨15953556926979507455968657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21271409235972676607958209 15953556926979507455968657)
            ·
              refine ⟨11965167695234630591976493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15953556926979507455968657 11965167695234630591976493)
              ·
                refine ⟨4486937885712986471991185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11965167695234630591976493 4486937885712986471991185)
                ·
                  refine ⟨3365203414284739853993389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4486937885712986471991185 3365203414284739853993389)
                  ·
                    refine ⟨1261951280356777445247521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3365203414284739853993389 1261951280356777445247521)
                    ·
                      refine ⟨946463460267583083935641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1261951280356777445247521 946463460267583083935641)
                      ·
                        rfl

theorem cell23_1843231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3, 2, 3, 2].length) (baseStart_1843231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1843231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1843231 prefixEnd_1843231 := by exact prefixLift 1843231
  have htrace : WordTrace (prefixWord ++ tailWord_1843231) baseStart_1843231 baseEnd_1843231 := by
    simpa [prefixWord, tailWord_1843231, baseEnd_1843231] using wordTrace_append hprefix tailTrace_1843231
  have hstable : (prefixWord ++ tailWord_1843231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843231).length < 2 ^ (prefixWord ++ tailWord_1843231).sum := by decide
  have hdescent : baseEnd_1843231 < baseStart_1843231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843264 : List Nat := [2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 5]
def baseStart_1843264 : Nat := 118140960795 + 1843264 * 2 ^ 59
def prefixEnd_1843264 : Nat := 4983230072969 + 3 ^ 40 * 1843264 * 2
def baseEnd_1843264 : Nat := 946480405129181454822989

theorem tailTrace_1843264 : CollatzResearch.WordTrace tailWord_1843264 prefixEnd_1843264 946480405129181454822989 := by
  unfold tailWord_1843264
  simp only [CollatzResearch.WordTrace]
  refine ⟨33614680597088403636724423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44819574129451204848965897 33614680597088403636724423)
  ·
    refine ⟨50422020895632605455086635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33614680597088403636724423 50422020895632605455086635)
    ·
      refine ⟨75633031343448908182629953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50422020895632605455086635 75633031343448908182629953)
      ·
        refine ⟨56724773507586681136972465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75633031343448908182629953 56724773507586681136972465)
        ·
          refine ⟨42543580130690010852729349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56724773507586681136972465 42543580130690010852729349)
          ·
            refine ⟨7976921274504377034886753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42543580130690010852729349 7976921274504377034886753)
            ·
              refine ⟨5982690955878282776165065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7976921274504377034886753 5982690955878282776165065)
              ·
                refine ⟨4487018216908712082123799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5982690955878282776165065 4487018216908712082123799)
                ·
                  refine ⟨6730527325363068123185699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4487018216908712082123799 6730527325363068123185699)
                  ·
                    refine ⟨10095790988044602184778549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6730527325363068123185699 10095790988044602184778549)
                    ·
                      refine ⟨946480405129181454822989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10095790988044602184778549 946480405129181454822989)
                      ·
                        rfl

theorem cell23_1843264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 5].length) (baseStart_1843264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1843264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1843264 prefixEnd_1843264 := by exact prefixLift 1843264
  have htrace : WordTrace (prefixWord ++ tailWord_1843264) baseStart_1843264 baseEnd_1843264 := by
    simpa [prefixWord, tailWord_1843264, baseEnd_1843264] using wordTrace_append hprefix tailTrace_1843264
  have hstable : (prefixWord ++ tailWord_1843264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843264).length < 2 ^ (prefixWord ++ tailWord_1843264).sum := by decide
  have hdescent : baseEnd_1843264 < baseStart_1843264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843271 : List Nat := [1, 1, 4, 1, 3, 1, 3, 3, 2, 4]
def baseStart_1843271 : Nat := 118140960795 + 1843271 * 2 ^ 59
def prefixEnd_1843271 : Nat := 4983230072969 + 3 ^ 40 * 1843271 * 2
def baseEnd_1843271 : Nat := 315494666497920975811819

theorem tailTrace_1843271 : CollatzResearch.WordTrace tailWord_1843271 prefixEnd_1843271 315494666497920975811819 := by
  unfold tailWord_1843271
  simp only [CollatzResearch.WordTrace]
  refine ⟨67229616505151447468953667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44819744336767631645969111 67229616505151447468953667)
  ·
    refine ⟨100844424757727171203430501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67229616505151447468953667 100844424757727171203430501)
    ·
      refine ⟨18908329642073844600643219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100844424757727171203430501 18908329642073844600643219)
      ·
        refine ⟨28362494463110766900964829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18908329642073844600643219 28362494463110766900964829)
        ·
          refine ⟨10635935423666537587861811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28362494463110766900964829 10635935423666537587861811)
          ·
            refine ⟨15953903135499806381792717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10635935423666537587861811 15953903135499806381792717)
            ·
              refine ⟨5982713675812427393172269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15953903135499806381792717 5982713675812427393172269)
              ·
                refine ⟨2243517628429660272439601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5982713675812427393172269 2243517628429660272439601)
                ·
                  refine ⟨1682638221322245204329701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2243517628429660272439601 1682638221322245204329701)
                  ·
                    refine ⟨315494666497920975811819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1682638221322245204329701 315494666497920975811819)
                    ·
                      rfl

theorem cell23_1843271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 3, 2, 4].length) (baseStart_1843271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1843271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1843271 prefixEnd_1843271 := by exact prefixLift 1843271
  have htrace : WordTrace (prefixWord ++ tailWord_1843271) baseStart_1843271 baseEnd_1843271 := by
    simpa [prefixWord, tailWord_1843271, baseEnd_1843271] using wordTrace_append hprefix tailTrace_1843271
  have hstable : (prefixWord ++ tailWord_1843271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843271).length < 2 ^ (prefixWord ++ tailWord_1843271).sum := by decide
  have hdescent : baseEnd_1843271 < baseStart_1843271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843274 : List Nat := [3, 1, 2, 1, 1, 2, 1, 5, 1, 2, 4]
def baseStart_1843274 : Nat := 118140960795 + 1843274 * 2 ^ 59
def prefixEnd_1843274 : Nat := 4983230072969 + 3 ^ 40 * 1843274 * 2
def baseEnd_1843274 : Nat := 946485539935726415697943

theorem tailTrace_1843274 : CollatzResearch.WordTrace tailWord_1843274 prefixEnd_1843274 946485539935726415697943 := by
  unfold tailWord_1843274
  simp only [CollatzResearch.WordTrace]
  refine ⟨16807431481035144745328219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44819817282760385987541917 16807431481035144745328219)
  ·
    refine ⟨25211147221552717117992329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16807431481035144745328219 25211147221552717117992329)
    ·
      refine ⟨18908360416164537838494247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25211147221552717117992329 18908360416164537838494247)
      ·
        refine ⟨28362540624246806757741371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18908360416164537838494247 28362540624246806757741371)
        ·
          refine ⟨42543810936370210136612057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28362540624246806757741371 42543810936370210136612057)
          ·
            refine ⟨31907858202277657602459043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42543810936370210136612057 31907858202277657602459043)
            ·
              refine ⟨47861787303416486403688565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31907858202277657602459043 47861787303416486403688565)
              ·
                refine ⟨4487042559695295600345803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47861787303416486403688565 4487042559695295600345803)
                ·
                  refine ⟨6730563839542943400518705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4487042559695295600345803 6730563839542943400518705)
                  ·
                    refine ⟨5047922879657207550389029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6730563839542943400518705 5047922879657207550389029)
                    ·
                      refine ⟨946485539935726415697943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5047922879657207550389029 946485539935726415697943)
                      ·
                        rfl

theorem cell23_1843274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5, 1, 2, 4].length) (baseStart_1843274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1843274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1843274 prefixEnd_1843274 := by exact prefixLift 1843274
  have htrace : WordTrace (prefixWord ++ tailWord_1843274) baseStart_1843274 baseEnd_1843274 := by
    simpa [prefixWord, tailWord_1843274, baseEnd_1843274] using wordTrace_append hprefix tailTrace_1843274
  have hstable : (prefixWord ++ tailWord_1843274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843274).length < 2 ^ (prefixWord ++ tailWord_1843274).sum := by decide
  have hdescent : baseEnd_1843274 < baseStart_1843274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843278 : List Nat := [4, 1, 1, 1, 1, 6, 1, 2, 1, 1, 4]
def baseStart_1843278 : Nat := 118140960795 + 1843278 * 2 ^ 59
def prefixEnd_1843278 : Nat := 4983230072969 + 3 ^ 40 * 1843278 * 2
def baseEnd_1843278 : Nat := 946487593858344400047925

theorem tailTrace_1843278 : CollatzResearch.WordTrace tailWord_1843278 prefixEnd_1843278 946487593858344400047925 := by
  unfold tailWord_1843278
  simp only [CollatzResearch.WordTrace]
  refine ⟨8403733977015760958057311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44819914544084058442972325 8403733977015760958057311)
  ·
    refine ⟨12605600965523641437085967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8403733977015760958057311 12605600965523641437085967)
    ·
      refine ⟨18908401448285462155628951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12605600965523641437085967 18908401448285462155628951)
      ·
        refine ⟨28362602172428193233443427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18908401448285462155628951 28362602172428193233443427)
        ·
          refine ⟨42543903258642289850165141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28362602172428193233443427 42543903258642289850165141)
          ·
            refine ⟨1994245465248857336726491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 42543903258642289850165141 1994245465248857336726491)
            ·
              refine ⟨2991368197873286005089737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1994245465248857336726491 2991368197873286005089737)
              ·
                refine ⟨2243526148404964503817303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2991368197873286005089737 2243526148404964503817303)
                ·
                  refine ⟨3365289222607446755725955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2243526148404964503817303 3365289222607446755725955)
                  ·
                    refine ⟨5047933833911170133588933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3365289222607446755725955 5047933833911170133588933)
                    ·
                      refine ⟨946487593858344400047925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5047933833911170133588933 946487593858344400047925)
                      ·
                        rfl

theorem cell23_1843278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 2, 1, 1, 4].length) (baseStart_1843278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1843278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1843278 prefixEnd_1843278 := by exact prefixLift 1843278
  have htrace : WordTrace (prefixWord ++ tailWord_1843278) baseStart_1843278 baseEnd_1843278 := by
    simpa [prefixWord, tailWord_1843278, baseEnd_1843278] using wordTrace_append hprefix tailTrace_1843278
  have hstable : (prefixWord ++ tailWord_1843278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843278).length < 2 ^ (prefixWord ++ tailWord_1843278).sum := by decide
  have hdescent : baseEnd_1843278 < baseStart_1843278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843307 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 7]
def baseStart_1843307 : Nat := 118140960795 + 1843307 * 2 ^ 59
def prefixEnd_1843307 : Nat := 4983230072969 + 3 ^ 40 * 1843307 * 2
def baseEnd_1843307 : Nat := 946502484797324786585291

theorem tailTrace_1843307 : CollatzResearch.WordTrace tailWord_1843307 prefixEnd_1843307 946502484797324786585291 := by
  unfold tailWord_1843307
  simp only [CollatzResearch.WordTrace]
  refine ⟨67230929533021025617264175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44820619688680683744842783 67230929533021025617264175)
  ·
    refine ⟨100846394299531538425896263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67230929533021025617264175 100846394299531538425896263)
    ·
      refine ⟨151269591449297307638844395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100846394299531538425896263 151269591449297307638844395)
      ·
        refine ⟨226904387173945961458266593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151269591449297307638844395 226904387173945961458266593)
        ·
          refine ⟨170178290380459471093699945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226904387173945961458266593 170178290380459471093699945)
          ·
            refine ⟨127633717785344603320274959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170178290380459471093699945 127633717785344603320274959)
            ·
              refine ⟨191450576678016904980412439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127633717785344603320274959 191450576678016904980412439)
              ·
                refine ⟨287175865017025357470618659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191450576678016904980412439 287175865017025357470618659)
                ·
                  refine ⟨430763797525538036205927989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 287175865017025357470618659 430763797525538036205927989)
                  ·
                    refine ⟨40384106018019190894305749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 430763797525538036205927989 40384106018019190894305749)
                    ·
                      refine ⟨946502484797324786585291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 40384106018019190894305749 946502484797324786585291)
                      ·
                        rfl

theorem cell23_1843307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 7].length) (baseStart_1843307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1843307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1843307 prefixEnd_1843307 := by exact prefixLift 1843307
  have htrace : WordTrace (prefixWord ++ tailWord_1843307) baseStart_1843307 baseEnd_1843307 := by
    simpa [prefixWord, tailWord_1843307, baseEnd_1843307] using wordTrace_append hprefix tailTrace_1843307
  have hstable : (prefixWord ++ tailWord_1843307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843307).length < 2 ^ (prefixWord ++ tailWord_1843307).sum := by decide
  have hdescent : baseEnd_1843307 < baseStart_1843307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843312 : List Nat := [2, 1, 1, 1, 5, 2, 4, 2, 1, 2, 2]
def baseStart_1843312 : Nat := 118140960795 + 1843312 * 2 ^ 59
def prefixEnd_1843312 : Nat := 4983230072969 + 3 ^ 40 * 1843312 * 2
def baseEnd_1843312 : Nat := 946505052200597267022769

theorem tailTrace_1843312 : CollatzResearch.WordTrace tailWord_1843312 prefixEnd_1843312 946505052200597267022769 := by
  unfold tailWord_1843312
  simp only [CollatzResearch.WordTrace]
  refine ⟨33615555949001455735598095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44820741265335274314130793 33615555949001455735598095)
  ·
    refine ⟨50423333923502183603397143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33615555949001455735598095 50423333923502183603397143)
    ·
      refine ⟨75635000885253275405095715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50423333923502183603397143 75635000885253275405095715)
      ·
        refine ⟨113452501327879913107643573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75635000885253275405095715 113452501327879913107643573)
        ·
          refine ⟨10636171999488741853841585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 113452501327879913107643573 10636171999488741853841585)
          ·
            refine ⟨7977128999616556390381189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10636171999488741853841585 7977128999616556390381189)
            ·
              refine ⟨1495711687428104323196473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7977128999616556390381189 1495711687428104323196473)
              ·
                refine ⟨1121783765571078242397355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1495711687428104323196473 1121783765571078242397355)
                ·
                  refine ⟨1682675648356617363596033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1121783765571078242397355 1682675648356617363596033)
                  ·
                    refine ⟨1262006736267463022697025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1682675648356617363596033 1262006736267463022697025)
                    ·
                      refine ⟨946505052200597267022769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1262006736267463022697025 946505052200597267022769)
                      ·
                        rfl

theorem cell23_1843312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 2, 1, 2, 2].length) (baseStart_1843312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1843312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1843312 prefixEnd_1843312 := by exact prefixLift 1843312
  have htrace : WordTrace (prefixWord ++ tailWord_1843312) baseStart_1843312 baseEnd_1843312 := by
    simpa [prefixWord, tailWord_1843312, baseEnd_1843312] using wordTrace_append hprefix tailTrace_1843312
  have hstable : (prefixWord ++ tailWord_1843312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843312).length < 2 ^ (prefixWord ++ tailWord_1843312).sum := by decide
  have hdescent : baseEnd_1843312 < baseStart_1843312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843314 : List Nat := [3, 2, 1, 2, 2, 2, 1, 1, 2, 7]
def baseStart_1843314 : Nat := 118140960795 + 1843314 * 2 ^ 59
def prefixEnd_1843314 : Nat := 4983230072969 + 3 ^ 40 * 1843314 * 2
def baseEnd_1843314 : Nat := 315502026387302086399253

theorem tailTrace_1843314 : CollatzResearch.WordTrace tailWord_1843314 prefixEnd_1843314 315502026387302086399253 := by
  unfold tailWord_1843314
  simp only [CollatzResearch.WordTrace]
  refine ⟨16807796210998916453192249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44820789895997110541845997 16807796210998916453192249)
  ·
    refine ⟨12605847158249187339894187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16807796210998916453192249 12605847158249187339894187)
    ·
      refine ⟨18908770737373781009841281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12605847158249187339894187 18908770737373781009841281)
      ·
        refine ⟨14181578053030335757380961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18908770737373781009841281 14181578053030335757380961)
        ·
          refine ⟨10636183539772751818035721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14181578053030335757380961 10636183539772751818035721)
          ·
            refine ⟨7977137654829563863526791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10636183539772751818035721 7977137654829563863526791)
            ·
              refine ⟨11965706482244345795290187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7977137654829563863526791 11965706482244345795290187)
              ·
                refine ⟨17948559723366518692935281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11965706482244345795290187 17948559723366518692935281)
                ·
                  refine ⟨13461419792524889019701461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17948559723366518692935281 13461419792524889019701461)
                  ·
                    refine ⟨315502026387302086399253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13461419792524889019701461 315502026387302086399253)
                    ·
                      rfl

theorem cell23_1843314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 2, 7].length) (baseStart_1843314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1843314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1843314 prefixEnd_1843314 := by exact prefixLift 1843314
  have htrace : WordTrace (prefixWord ++ tailWord_1843314) baseStart_1843314 baseEnd_1843314 := by
    simpa [prefixWord, tailWord_1843314, baseEnd_1843314] using wordTrace_append hprefix tailTrace_1843314
  have hstable : (prefixWord ++ tailWord_1843314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843314).length < 2 ^ (prefixWord ++ tailWord_1843314).sum := by decide
  have hdescent : baseEnd_1843314 < baseStart_1843314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843338 : List Nat := [3, 1, 2, 3, 1, 2, 2, 1, 3, 3, 2]
def baseStart_1843338 : Nat := 118140960795 + 1843338 * 2 ^ 59
def prefixEnd_1843338 : Nat := 4983230072969 + 3 ^ 40 * 1843338 * 2
def baseEnd_1843338 : Nat := 946518402697614165297649

theorem tailTrace_1843338 : CollatzResearch.WordTrace tailWord_1843338 prefixEnd_1843338 946518402697614165297649 := by
  unfold tailWord_1843338
  simp only [CollatzResearch.WordTrace]
  refine ⟨16808015048977179477910667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44821373463939145274428445 16808015048977179477910667)
  ·
    refine ⟨25212022573465769216866001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16808015048977179477910667 25212022573465769216866001)
    ·
      refine ⟨18909016930099326912649501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25212022573465769216866001 18909016930099326912649501)
      ·
        refine ⟨7090881348787247592243563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18909016930099326912649501 7090881348787247592243563)
        ·
          refine ⟨10636322023180871388365345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7090881348787247592243563 10636322023180871388365345)
          ·
            refine ⟨7977241517385653541274009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10636322023180871388365345 7977241517385653541274009)
            ·
              refine ⟨5982931138039240155955507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7977241517385653541274009 5982931138039240155955507)
              ·
                refine ⟨8974396707058860233933261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5982931138039240155955507 8974396707058860233933261)
                ·
                  refine ⟨3365398765147072587724973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8974396707058860233933261 3365398765147072587724973)
                  ·
                    refine ⟨1262024536930152220396865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3365398765147072587724973 1262024536930152220396865)
                    ·
                      refine ⟨946518402697614165297649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1262024536930152220396865 946518402697614165297649)
                      ·
                        rfl

theorem cell23_1843338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_1843338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1843338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1843338 prefixEnd_1843338 := by exact prefixLift 1843338
  have htrace : WordTrace (prefixWord ++ tailWord_1843338) baseStart_1843338 baseEnd_1843338 := by
    simpa [prefixWord, tailWord_1843338, baseEnd_1843338] using wordTrace_append hprefix tailTrace_1843338
  have hstable : (prefixWord ++ tailWord_1843338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843338).length < 2 ^ (prefixWord ++ tailWord_1843338).sum := by decide
  have hdescent : baseEnd_1843338 < baseStart_1843338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843362 : List Nat := [3, 3, 1, 3, 1, 3, 1, 2, 2, 1, 3]
def baseStart_1843362 : Nat := 118140960795 + 1843362 * 2 ^ 59
def prefixEnd_1843362 : Nat := 4983230072969 + 3 ^ 40 * 1843362 * 2
def baseEnd_1843362 : Nat := 946530726233322071397539

theorem tailTrace_1843362 : CollatzResearch.WordTrace tailWord_1843362 prefixEnd_1843362 946530726233322071397539 := by
  unfold tailWord_1843362
  simp only [CollatzResearch.WordTrace]
  refine ⟨16808233886955442502629085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44821957031881180007010893 16808233886955442502629085)
  ·
    refine ⟨6303087707608290938485907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16808233886955442502629085 6303087707608290938485907)
    ·
      refine ⟨9454631561412436407728861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6303087707608290938485907 9454631561412436407728861)
      ·
        refine ⟨3545486835529663652898323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9454631561412436407728861 3545486835529663652898323)
        ·
          refine ⟨5318230253294495479347485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3545486835529663652898323 5318230253294495479347485)
          ·
            refine ⟨1994336344985435804755307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5318230253294495479347485 1994336344985435804755307)
            ·
              refine ⟨2991504517478153707132961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1994336344985435804755307 2991504517478153707132961)
              ·
                refine ⟨2243628388108615280349721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2991504517478153707132961 2243628388108615280349721)
                ·
                  refine ⟨1682721291081461460262291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2243628388108615280349721 1682721291081461460262291)
                  ·
                    refine ⟨2524081936622192190393437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1682721291081461460262291 2524081936622192190393437)
                    ·
                      refine ⟨946530726233322071397539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2524081936622192190393437 946530726233322071397539)
                      ·
                        rfl

theorem cell23_1843362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_1843362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1843362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1843362 prefixEnd_1843362 := by exact prefixLift 1843362
  have htrace : WordTrace (prefixWord ++ tailWord_1843362) baseStart_1843362 baseEnd_1843362 := by
    simpa [prefixWord, tailWord_1843362, baseEnd_1843362] using wordTrace_append hprefix tailTrace_1843362
  have hstable : (prefixWord ++ tailWord_1843362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843362).length < 2 ^ (prefixWord ++ tailWord_1843362).sum := by decide
  have hdescent : baseEnd_1843362 < baseStart_1843362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843431 : List Nat := [1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 7]
def baseStart_1843431 : Nat := 118140960795 + 1843431 * 2 ^ 59
def prefixEnd_1843431 : Nat := 4983230072969 + 3 ^ 40 * 1843431 * 2
def baseEnd_1843431 : Nat := 946566156398482301434721

theorem tailTrace_1843431 : CollatzResearch.WordTrace tailWord_1843431 prefixEnd_1843431 946566156398482301434721 := by
  unfold tailWord_1843431
  simp only [CollatzResearch.WordTrace]
  refine ⟨67235452184571794794778147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44823634789714529863185431 67235452184571794794778147)
  ·
    refine ⟨100853178276857692192167221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67235452184571794794778147 100853178276857692192167221)
    ·
      refine ⟨9454985463455408643015677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100853178276857692192167221 9454985463455408643015677)
      ·
        refine ⟨3545619548795778241130879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9454985463455408643015677 3545619548795778241130879)
        ·
          refine ⟨5318429323193667361696319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3545619548795778241130879 5318429323193667361696319)
          ·
            refine ⟨7977643984790501042544479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5318429323193667361696319 7977643984790501042544479)
            ·
              refine ⟨11966465977185751563816719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7977643984790501042544479 11966465977185751563816719)
              ·
                refine ⟨17949698965778627345725079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11966465977185751563816719 17949698965778627345725079)
                ·
                  refine ⟨26924548448667941018587619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17949698965778627345725079 26924548448667941018587619)
                  ·
                    refine ⟨40386822673001911527881429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26924548448667941018587619 40386822673001911527881429)
                    ·
                      refine ⟨946566156398482301434721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 40386822673001911527881429 946566156398482301434721)
                      ·
                        rfl

theorem cell23_1843431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_1843431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1843431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1843431 prefixEnd_1843431 := by exact prefixLift 1843431
  have htrace : WordTrace (prefixWord ++ tailWord_1843431) baseStart_1843431 baseEnd_1843431 := by
    simpa [prefixWord, tailWord_1843431, baseEnd_1843431] using wordTrace_append hprefix tailTrace_1843431
  have hstable : (prefixWord ++ tailWord_1843431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843431).length < 2 ^ (prefixWord ++ tailWord_1843431).sum := by decide
  have hdescent : baseEnd_1843431 < baseStart_1843431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843502 : List Nat := [4, 1, 3, 3, 1, 1, 1, 2, 3, 4]
def baseStart_1843502 : Nat := 118140960795 + 1843502 * 2 ^ 59
def prefixEnd_1843502 : Nat := 4983230072969 + 3 ^ 40 * 1843502 * 2
def baseEnd_1843502 : Nat := 315534204508317174548965

theorem tailTrace_1843502 : CollatzResearch.WordTrace tailWord_1843502 prefixEnd_1843502 315534204508317174548965 := by
  unfold tailWord_1843502
  simp only [CollatzResearch.WordTrace]
  refine ⟨8404755220914321740076595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44825361178209715947075173 8404755220914321740076595)
  ·
    refine ⟨12607132831371482610114893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8404755220914321740076595 12607132831371482610114893)
    ·
      refine ⟨4727674811764305978793085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12607132831371482610114893 4727674811764305978793085)
      ·
        refine ⟨1772878054411614742047407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4727674811764305978793085 1772878054411614742047407)
        ·
          refine ⟨2659317081617422113071111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1772878054411614742047407 2659317081617422113071111)
          ·
            refine ⟨3988975622426133169606667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2659317081617422113071111 3988975622426133169606667)
            ·
              refine ⟨5983463433639199754410001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3988975622426133169606667 5983463433639199754410001)
              ·
                refine ⟨4487597575229399815807501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5983463433639199754410001 4487597575229399815807501)
                ·
                  refine ⟨1682849090711024930927813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4487597575229399815807501 1682849090711024930927813)
                  ·
                    refine ⟨315534204508317174548965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1682849090711024930927813 315534204508317174548965)
                    ·
                      rfl

theorem cell23_1843502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_1843502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1843502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1843502 prefixEnd_1843502 := by exact prefixLift 1843502
  have htrace : WordTrace (prefixWord ++ tailWord_1843502) baseStart_1843502 baseEnd_1843502 := by
    simpa [prefixWord, tailWord_1843502, baseEnd_1843502] using wordTrace_append hprefix tailTrace_1843502
  have hstable : (prefixWord ++ tailWord_1843502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843502).length < 2 ^ (prefixWord ++ tailWord_1843502).sum := by decide
  have hdescent : baseEnd_1843502 < baseStart_1843502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843531 : List Nat := [1, 1, 1, 1, 3, 1, 1, 4, 5, 1, 4]
def baseStart_1843531 : Nat := 118140960795 + 1843531 * 2 ^ 59
def prefixEnd_1843531 : Nat := 4983230072969 + 3 ^ 40 * 1843531 * 2
def baseEnd_1843531 : Nat := 946617504463931910184261

theorem tailTrace_1843531 : CollatzResearch.WordTrace tailWord_1843531 prefixEnd_1843531 946617504463931910184261 := by
  unfold tailWord_1843531
  simp only [CollatzResearch.WordTrace]
  refine ⟨67239099484209511873418447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44826066322806341248945631 67239099484209511873418447)
  ·
    refine ⟨100858649226314267810127671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67239099484209511873418447 100858649226314267810127671)
    ·
      refine ⟨151287973839471401715191507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100858649226314267810127671 151287973839471401715191507)
      ·
        refine ⟨226931960759207102572787261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151287973839471401715191507 226931960759207102572787261)
        ·
          refine ⟨85099485284702663464795223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226931960759207102572787261 85099485284702663464795223)
          ·
            refine ⟨127649227927053995197192835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85099485284702663464795223 127649227927053995197192835)
            ·
              refine ⟨191473841890580992795789253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127649227927053995197192835 191473841890580992795789253)
              ·
                refine ⟨35901345354483936149210485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 191473841890580992795789253 35901345354483936149210485)
                ·
                  refine ⟨3365751126982869013988483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35901345354483936149210485 3365751126982869013988483)
                  ·
                    refine ⟨5048626690474303520982725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3365751126982869013988483 5048626690474303520982725)
                    ·
                      refine ⟨946617504463931910184261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5048626690474303520982725 946617504463931910184261)
                      ·
                        rfl

theorem cell23_1843531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 5, 1, 4].length) (baseStart_1843531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1843531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1843531 prefixEnd_1843531 := by exact prefixLift 1843531
  have htrace : WordTrace (prefixWord ++ tailWord_1843531) baseStart_1843531 baseEnd_1843531 := by
    simpa [prefixWord, tailWord_1843531, baseEnd_1843531] using wordTrace_append hprefix tailTrace_1843531
  have hstable : (prefixWord ++ tailWord_1843531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843531).length < 2 ^ (prefixWord ++ tailWord_1843531).sum := by decide
  have hdescent : baseEnd_1843531 < baseStart_1843531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843551 : List Nat := [1, 1, 2, 3, 1, 2, 3, 1, 3, 1, 5]
def baseStart_1843551 : Nat := 118140960795 + 1843551 * 2 ^ 59
def prefixEnd_1843551 : Nat := 4983230072969 + 3 ^ 40 * 1843551 * 2
def baseEnd_1843551 : Nat := 946627774077021831934169

theorem tailTrace_1843551 : CollatzResearch.WordTrace tailWord_1843551 prefixEnd_1843551 946627774077021831934169 := by
  unfold tailWord_1843551
  simp only [CollatzResearch.WordTrace]
  refine ⟨67239828944137055289146507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44826552629424703526097671 67239828944137055289146507)
  ·
    refine ⟨100859743416205582933719761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67239828944137055289146507 100859743416205582933719761)
    ·
      refine ⟨75644807562154187200289821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100859743416205582933719761 75644807562154187200289821)
      ·
        refine ⟨28366802835807820200108683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75644807562154187200289821 28366802835807820200108683)
        ·
          refine ⟨42550204253711730300163025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28366802835807820200108683 42550204253711730300163025)
          ·
            refine ⟨31912653190283797725122269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42550204253711730300163025 31912653190283797725122269)
            ·
              refine ⟨11967244946356424146920851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31912653190283797725122269 11967244946356424146920851)
              ·
                refine ⟨17950867419534636220381277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11967244946356424146920851 17950867419534636220381277)
                ·
                  refine ⟨6731575282325488582642979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17950867419534636220381277 6731575282325488582642979)
                  ·
                    refine ⟨10097362923488232873964469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6731575282325488582642979 10097362923488232873964469)
                    ·
                      refine ⟨946627774077021831934169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10097362923488232873964469 946627774077021831934169)
                      ·
                        rfl

theorem cell23_1843551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_1843551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1843551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1843551 prefixEnd_1843551 := by exact prefixLift 1843551
  have htrace : WordTrace (prefixWord ++ tailWord_1843551) baseStart_1843551 baseEnd_1843551 := by
    simpa [prefixWord, tailWord_1843551, baseEnd_1843551] using wordTrace_append hprefix tailTrace_1843551
  have hstable : (prefixWord ++ tailWord_1843551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843551).length < 2 ^ (prefixWord ++ tailWord_1843551).sum := by decide
  have hdescent : baseEnd_1843551 < baseStart_1843551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843561 : List Nat := [1, 2, 1, 1, 1, 3, 5, 1, 1, 1, 6]
def baseStart_1843561 : Nat := 118140960795 + 1843561 * 2 ^ 59
def prefixEnd_1843561 : Nat := 4983230072969 + 3 ^ 40 * 1843561 * 2
def baseEnd_1843561 : Nat := 946632908883566792809123

theorem tailTrace_1843561 : CollatzResearch.WordTrace tailWord_1843561 prefixEnd_1843561 946632908883566792809123 := by
  unfold tailWord_1843561
  simp only [CollatzResearch.WordTrace]
  refine ⟨67240193674100826997010537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44826795782733884664673691 67240193674100826997010537)
  ·
    refine ⟨50430145255575620247757903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67240193674100826997010537 50430145255575620247757903)
    ·
      refine ⟨75645217883363430371636855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50430145255575620247757903 75645217883363430371636855)
      ·
        refine ⟨113467826825045145557455283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75645217883363430371636855 113467826825045145557455283)
        ·
          refine ⟨170201740237567718336182925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113467826825045145557455283 170201740237567718336182925)
          ·
            refine ⟨63825652589087894376068597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170201740237567718336182925 63825652589087894376068597)
            ·
              refine ⟨5983654930226990097756431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63825652589087894376068597 5983654930226990097756431)
              ·
                refine ⟨8975482395340485146634647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5983654930226990097756431 8975482395340485146634647)
                ·
                  refine ⟨13463223593010727719951971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8975482395340485146634647 13463223593010727719951971)
                  ·
                    refine ⟨20194835389516091579927957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13463223593010727719951971 20194835389516091579927957)
                    ·
                      refine ⟨946632908883566792809123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20194835389516091579927957 946632908883566792809123)
                      ·
                        rfl

theorem cell23_1843561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 1, 6].length) (baseStart_1843561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1843561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1843561 prefixEnd_1843561 := by exact prefixLift 1843561
  have htrace : WordTrace (prefixWord ++ tailWord_1843561) baseStart_1843561 baseEnd_1843561 := by
    simpa [prefixWord, tailWord_1843561, baseEnd_1843561] using wordTrace_append hprefix tailTrace_1843561
  have hstable : (prefixWord ++ tailWord_1843561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843561).length < 2 ^ (prefixWord ++ tailWord_1843561).sum := by decide
  have hdescent : baseEnd_1843561 < baseStart_1843561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843565 : List Nat := [1, 5, 1, 1, 1, 2, 4, 2, 1, 1, 4]
def baseStart_1843565 : Nat := 118140960795 + 1843565 * 2 ^ 59
def prefixEnd_1843565 : Nat := 4983230072969 + 3 ^ 40 * 1843565 * 2
def baseEnd_1843565 : Nat := 946634962806184777159105

theorem tailTrace_1843565 : CollatzResearch.WordTrace tailWord_1843565 prefixEnd_1843565 946634962806184777159105 := by
  unfold tailWord_1843565
  simp only [CollatzResearch.WordTrace]
  refine ⟨67240339566086335680156149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44826893044057557120104099 67240339566086335680156149)
  ·
    refine ⟨6303781834320593970014639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67240339566086335680156149 6303781834320593970014639)
    ·
      refine ⟨9455672751480890955021959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6303781834320593970014639 9455672751480890955021959)
      ·
        refine ⟨14183509127221336432532939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9455672751480890955021959 14183509127221336432532939)
        ·
          refine ⟨21275263690832004648799409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14183509127221336432532939 21275263690832004648799409)
          ·
            refine ⟨15956447768124003486599557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21275263690832004648799409 15956447768124003486599557)
            ·
              refine ⟨2991833956523250653737417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15956447768124003486599557 2991833956523250653737417)
              ·
                refine ⟨2243875467392437990303063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2991833956523250653737417 2243875467392437990303063)
                ·
                  refine ⟨3365813201088656985454595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2243875467392437990303063 3365813201088656985454595)
                  ·
                    refine ⟨5048719801632985478181893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3365813201088656985454595 5048719801632985478181893)
                    ·
                      refine ⟨946634962806184777159105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5048719801632985478181893 946634962806184777159105)
                      ·
                        rfl

theorem cell23_1843565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_1843565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1843565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1843565 prefixEnd_1843565 := by exact prefixLift 1843565
  have htrace : WordTrace (prefixWord ++ tailWord_1843565) baseStart_1843565 baseEnd_1843565 := by
    simpa [prefixWord, tailWord_1843565, baseEnd_1843565] using wordTrace_append hprefix tailTrace_1843565
  have hstable : (prefixWord ++ tailWord_1843565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843565).length < 2 ^ (prefixWord ++ tailWord_1843565).sum := by decide
  have hdescent : baseEnd_1843565 < baseStart_1843565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843585 : List Nat := [1, 2, 4, 3, 1, 2, 2, 1, 1, 1, 5]
def baseStart_1843585 : Nat := 118140960795 + 1843585 * 2 ^ 59
def prefixEnd_1843585 : Nat := 4983230072969 + 3 ^ 40 * 1843585 * 2
def baseEnd_1843585 : Nat := 946645232419274698909013

theorem tailTrace_1843585 : CollatzResearch.WordTrace tailWord_1843585 prefixEnd_1843585 946645232419274698909013 := by
  unfold tailWord_1843585
  simp only [CollatzResearch.WordTrace]
  refine ⟨67241069026013879095884209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44827379350675919397256139 67241069026013879095884209)
  ·
    refine ⟨50430801769510409321913157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67241069026013879095884209 50430801769510409321913157)
    ·
      refine ⟨9455775331783201747858717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50430801769510409321913157 9455775331783201747858717)
      ·
        refine ⟨3545915749418700655447019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9455775331783201747858717 3545915749418700655447019)
        ·
          refine ⟨5318873624128050983170529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3545915749418700655447019 5318873624128050983170529)
          ·
            refine ⟨3989155218096038237377897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5318873624128050983170529 3989155218096038237377897)
            ·
              refine ⟨2991866413572028678033423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3989155218096038237377897 2991866413572028678033423)
              ·
                refine ⟨4487799620358043017050135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2991866413572028678033423 4487799620358043017050135)
                ·
                  refine ⟨6731699430537064525575203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4487799620358043017050135 6731699430537064525575203)
                  ·
                    refine ⟨10097549145805596788362805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6731699430537064525575203 10097549145805596788362805)
                    ·
                      refine ⟨946645232419274698909013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10097549145805596788362805 946645232419274698909013)
                      ·
                        rfl

theorem cell23_1843585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_1843585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1843585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1843585 prefixEnd_1843585 := by exact prefixLift 1843585
  have htrace : WordTrace (prefixWord ++ tailWord_1843585) baseStart_1843585 baseEnd_1843585 := by
    simpa [prefixWord, tailWord_1843585, baseEnd_1843585] using wordTrace_append hprefix tailTrace_1843585
  have hstable : (prefixWord ++ tailWord_1843585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843585).length < 2 ^ (prefixWord ++ tailWord_1843585).sum := by decide
  have hdescent : baseEnd_1843585 < baseStart_1843585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843631 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 6, 6]
def baseStart_1843631 : Nat := 118140960795 + 1843631 * 2 ^ 59
def prefixEnd_1843631 : Nat := 4983230072969 + 3 ^ 40 * 1843631 * 2
def baseEnd_1843631 : Nat := 315556284176460506311267

theorem tailTrace_1843631 : CollatzResearch.WordTrace tailWord_1843631 prefixEnd_1843631 315556284176460506311267 := by
  unfold tailWord_1843631
  simp only [CollatzResearch.WordTrace]
  refine ⟨67242746783847228952058747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44828497855898152634705831 67242746783847228952058747)
  ·
    refine ⟨100864120175770843428088121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67242746783847228952058747 100864120175770843428088121)
    ·
      refine ⟨75648090131828132571066091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100864120175770843428088121 75648090131828132571066091)
      ·
        refine ⟨113472135197742198856599137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75648090131828132571066091 113472135197742198856599137)
        ·
          refine ⟨85104101398306649142449353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113472135197742198856599137 85104101398306649142449353)
          ·
            refine ⟨63828076048729986856837015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85104101398306649142449353 63828076048729986856837015)
            ·
              refine ⟨95742114073094980285255523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63828076048729986856837015 95742114073094980285255523)
              ·
                refine ⟨143613171109642470427883285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95742114073094980285255523 143613171109642470427883285)
                ·
                  refine ⟨6731867395764490801307029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 143613171109642470427883285 6731867395764490801307029)
                  ·
                    refine ⟨315556284176460506311267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6731867395764490801307029 315556284176460506311267)
                    ·
                      rfl

theorem cell23_1843631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6, 6].length) (baseStart_1843631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1843631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1843631 prefixEnd_1843631 := by exact prefixLift 1843631
  have htrace : WordTrace (prefixWord ++ tailWord_1843631) baseStart_1843631 baseEnd_1843631 := by
    simpa [prefixWord, tailWord_1843631, baseEnd_1843631] using wordTrace_append hprefix tailTrace_1843631
  have hstable : (prefixWord ++ tailWord_1843631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843631).length < 2 ^ (prefixWord ++ tailWord_1843631).sum := by decide
  have hdescent : baseEnd_1843631 < baseStart_1843631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843636 : List Nat := [2, 5, 2, 2, 2, 1, 1, 1, 1, 1, 5]
def baseStart_1843636 : Nat := 118140960795 + 1843636 * 2 ^ 59
def prefixEnd_1843636 : Nat := 4983230072969 + 3 ^ 40 * 1843636 * 2
def baseEnd_1843636 : Nat := 946671419932653999371279

theorem tailTrace_1843636 : CollatzResearch.WordTrace tailWord_1843636 prefixEnd_1843636 946671419932653999371279 := by
  unfold tailWord_1843636
  simp only [CollatzResearch.WordTrace]
  refine ⟨33621464574414557402995381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44828619432552743203993841 33621464574414557402995381)
  ·
    refine ⟨3152012303851364756530817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33621464574414557402995381 3152012303851364756530817)
    ·
      refine ⟨2364009227888523567398113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3152012303851364756530817 2364009227888523567398113)
      ·
        refine ⟨1773006920916392675548585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2364009227888523567398113 1773006920916392675548585)
        ·
          refine ⟨1329755190687294506661439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1773006920916392675548585 1329755190687294506661439)
          ·
            refine ⟨1994632786030941759992159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1329755190687294506661439 1994632786030941759992159)
            ·
              refine ⟨2991949179046412639988239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1994632786030941759992159 2991949179046412639988239)
              ·
                refine ⟨4487923768569618959982359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2991949179046412639988239 4487923768569618959982359)
                ·
                  refine ⟨6731885652854428439973539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4487923768569618959982359 6731885652854428439973539)
                  ·
                    refine ⟨10097828479281642659960309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6731885652854428439973539 10097828479281642659960309)
                    ·
                      refine ⟨946671419932653999371279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10097828479281642659960309 946671419932653999371279)
                      ·
                        rfl

theorem cell23_1843636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_1843636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1843636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1843636 prefixEnd_1843636 := by exact prefixLift 1843636
  have htrace : WordTrace (prefixWord ++ tailWord_1843636) baseStart_1843636 baseEnd_1843636 := by
    simpa [prefixWord, tailWord_1843636, baseEnd_1843636] using wordTrace_append hprefix tailTrace_1843636
  have hstable : (prefixWord ++ tailWord_1843636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843636).length < 2 ^ (prefixWord ++ tailWord_1843636).sum := by decide
  have hdescent : baseEnd_1843636 < baseStart_1843636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843651 : List Nat := [1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 6]
def baseStart_1843651 : Nat := 118140960795 + 1843651 * 2 ^ 59
def prefixEnd_1843651 : Nat := 4983230072969 + 3 ^ 40 * 1843651 * 2
def baseEnd_1843651 : Nat := 946679122142471440683709

theorem tailTrace_1843651 : CollatzResearch.WordTrace tailWord_1843651 prefixEnd_1843651 946679122142471440683709 := by
  unfold tailWord_1843651
  simp only [CollatzResearch.WordTrace]
  refine ⟨67243476243774772367786807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44828984162516514911857871 67243476243774772367786807)
  ·
    refine ⟨100865214365662158551680211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67243476243774772367786807 100865214365662158551680211)
    ·
      refine ⟨151297821548493237827520317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100865214365662158551680211 151297821548493237827520317)
      ·
        refine ⟨56736683080684964185320119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151297821548493237827520317 56736683080684964185320119)
        ·
          refine ⟨85105024621027446277980179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56736683080684964185320119 85105024621027446277980179)
          ·
            refine ⟨127657536931541169416970269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85105024621027446277980179 127657536931541169416970269)
            ·
              refine ⟨47871576349327938531363851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127657536931541169416970269 47871576349327938531363851)
              ·
                refine ⟨71807364523991907797045777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47871576349327938531363851 71807364523991907797045777)
                ·
                  refine ⟨53855523392993930847784333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71807364523991907797045777 53855523392993930847784333)
                  ·
                    refine ⟨20195821272372724067919125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53855523392993930847784333 20195821272372724067919125)
                    ·
                      refine ⟨946679122142471440683709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20195821272372724067919125 946679122142471440683709)
                      ·
                        rfl

theorem cell23_1843651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 6].length) (baseStart_1843651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1843651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1843651 prefixEnd_1843651 := by exact prefixLift 1843651
  have htrace : WordTrace (prefixWord ++ tailWord_1843651) baseStart_1843651 baseEnd_1843651 := by
    simpa [prefixWord, tailWord_1843651, baseEnd_1843651] using wordTrace_append hprefix tailTrace_1843651
  have hstable : (prefixWord ++ tailWord_1843651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843651).length < 2 ^ (prefixWord ++ tailWord_1843651).sum := by decide
  have hdescent : baseEnd_1843651 < baseStart_1843651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843658 : List Nat := [3, 1, 2, 1, 2, 2, 1, 1, 1, 6, 3]
def baseStart_1843658 : Nat := 118140960795 + 1843658 * 2 ^ 59
def prefixEnd_1843658 : Nat := 4983230072969 + 3 ^ 40 * 1843658 * 2
def baseEnd_1843658 : Nat := 946682716507052913296177

theorem tailTrace_1843658 : CollatzResearch.WordTrace tailWord_1843658 prefixEnd_1843658 946682716507052913296177 := by
  unfold tailWord_1843658
  simp only [CollatzResearch.WordTrace]
  refine ⟨16810932888687353140822907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44829154369832941708861085 16810932888687353140822907)
  ·
    refine ⟨25216399333031029711234361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16810932888687353140822907 25216399333031029711234361)
    ·
      refine ⟨18912299499773272283425771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25216399333031029711234361 18912299499773272283425771)
      ·
        refine ⟨28368449249659908425138657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18912299499773272283425771 28368449249659908425138657)
        ·
          refine ⟨21276336937244931318853993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28368449249659908425138657 21276336937244931318853993)
          ·
            refine ⟨15957252702933698489140495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21276336937244931318853993 15957252702933698489140495)
            ·
              refine ⟨23935879054400547733710743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15957252702933698489140495 23935879054400547733710743)
              ·
                refine ⟨35903818581600821600566115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23935879054400547733710743 35903818581600821600566115)
                ·
                  refine ⟨53855727872401232400849173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35903818581600821600566115 53855727872401232400849173)
                  ·
                    refine ⟨2524487244018807768789805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 53855727872401232400849173 2524487244018807768789805)
                    ·
                      refine ⟨946682716507052913296177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2524487244018807768789805 946682716507052913296177)
                      ·
                        rfl

theorem cell23_1843658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 1, 6, 3].length) (baseStart_1843658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1843658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1843658 prefixEnd_1843658 := by exact prefixLift 1843658
  have htrace : WordTrace (prefixWord ++ tailWord_1843658) baseStart_1843658 baseEnd_1843658 := by
    simpa [prefixWord, tailWord_1843658, baseEnd_1843658] using wordTrace_append hprefix tailTrace_1843658
  have hstable : (prefixWord ++ tailWord_1843658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843658).length < 2 ^ (prefixWord ++ tailWord_1843658).sum := by decide
  have hdescent : baseEnd_1843658 < baseStart_1843658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843708 : List Nat := [2, 2, 2, 1, 2, 1, 1, 3, 4, 5]
def baseStart_1843708 : Nat := 118140960795 + 1843708 * 2 ^ 59
def prefixEnd_1843708 : Nat := 4983230072969 + 3 ^ 40 * 1843708 * 2
def baseEnd_1843708 : Nat := 315569463513259239223649

theorem tailTrace_1843708 : CollatzResearch.WordTrace tailWord_1843708 prefixEnd_1843708 315569463513259239223649 := by
  unfold tailWord_1843708
  simp only [CollatzResearch.WordTrace]
  refine ⟨33622777602284135551305889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44830370136378847401741185 33622777602284135551305889)
  ·
    refine ⟨25217083201713101663479417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33622777602284135551305889 25217083201713101663479417)
    ·
      refine ⟨18912812401284826247609563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25217083201713101663479417 18912812401284826247609563)
      ·
        refine ⟨28369218601927239371414345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18912812401284826247609563 28369218601927239371414345)
        ·
          refine ⟨21276913951445429528560759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28369218601927239371414345 21276913951445429528560759)
          ·
            refine ⟨31915370927168144292841139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21276913951445429528560759 31915370927168144292841139)
            ·
              refine ⟨47873056390752216439261709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31915370927168144292841139 47873056390752216439261709)
              ·
                refine ⟨17952396146532081164723141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47873056390752216439261709 17952396146532081164723141)
                ·
                  refine ⟨3366074277474765218385589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17952396146532081164723141 3366074277474765218385589)
                  ·
                    refine ⟨315569463513259239223649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3366074277474765218385589 315569463513259239223649)
                    ·
                      rfl

theorem cell23_1843708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 4, 5].length) (baseStart_1843708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1843708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1843708 prefixEnd_1843708 := by exact prefixLift 1843708
  have htrace : WordTrace (prefixWord ++ tailWord_1843708) baseStart_1843708 baseEnd_1843708 := by
    simpa [prefixWord, tailWord_1843708, baseEnd_1843708] using wordTrace_append hprefix tailTrace_1843708
  have hstable : (prefixWord ++ tailWord_1843708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843708).length < 2 ^ (prefixWord ++ tailWord_1843708).sum := by decide
  have hdescent : baseEnd_1843708 < baseStart_1843708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843745 : List Nat := [1, 2, 3, 2, 2, 1, 2, 3, 2, 1, 4]
def baseStart_1843745 : Nat := 118140960795 + 1843745 * 2 ^ 59
def prefixEnd_1843745 : Nat := 4983230072969 + 3 ^ 40 * 1843745 * 2
def baseEnd_1843745 : Nat := 946727389323994072908277

theorem tailTrace_1843745 : CollatzResearch.WordTrace tailWord_1843745 prefixEnd_1843745 946727389323994072908277 := by
  unfold tailWord_1843745
  simp only [CollatzResearch.WordTrace]
  refine ⟨67246904705434226421708689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44831269803622817614472459 67246904705434226421708689)
  ·
    refine ⟨50435178529075669816281517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67246904705434226421708689 50435178529075669816281517)
    ·
      refine ⟨18913191948403376181105569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50435178529075669816281517 18913191948403376181105569)
      ·
        refine ⟨14184893961302532135829177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18913191948403376181105569 14184893961302532135829177)
        ·
          refine ⟨10638670470976899101871883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14184893961302532135829177 10638670470976899101871883)
          ·
            refine ⟨15958005706465348652807825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10638670470976899101871883 15958005706465348652807825)
            ·
              refine ⟨11968504279849011489605869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15958005706465348652807825 11968504279849011489605869)
              ·
                refine ⟨4488189104943379308602201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11968504279849011489605869 4488189104943379308602201)
                ·
                  refine ⟨3366141828707534481451651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4488189104943379308602201 3366141828707534481451651)
                  ·
                    refine ⟨5049212743061301722177477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3366141828707534481451651 5049212743061301722177477)
                    ·
                      refine ⟨946727389323994072908277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5049212743061301722177477 946727389323994072908277)
                      ·
                        rfl

theorem cell23_1843745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_1843745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1843745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1843745 prefixEnd_1843745 := by exact prefixLift 1843745
  have htrace : WordTrace (prefixWord ++ tailWord_1843745) baseStart_1843745 baseEnd_1843745 := by
    simpa [prefixWord, tailWord_1843745, baseEnd_1843745] using wordTrace_append hprefix tailTrace_1843745
  have hstable : (prefixWord ++ tailWord_1843745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843745).length < 2 ^ (prefixWord ++ tailWord_1843745).sum := by decide
  have hdescent : baseEnd_1843745 < baseStart_1843745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843768 : List Nat := [2, 1, 2, 1, 4, 1, 1, 3, 8]
def baseStart_1843768 : Nat := 118140960795 + 1843768 * 2 ^ 59
def prefixEnd_1843768 : Nat := 4983230072969 + 3 ^ 40 * 1843768 * 2
def baseEnd_1843768 : Nat := 105193244375449720324519

theorem tailTrace_1843768 : CollatzResearch.WordTrace tailWord_1843768 prefixEnd_1843768 105193244375449720324519 := by
  unfold tailWord_1843768
  simp only [CollatzResearch.WordTrace]
  refine ⟨33623871792175450674897979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44831829056233934233197305 33623871792175450674897979)
  ·
    refine ⟨50435807688263176012346969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33623871792175450674897979 50435807688263176012346969)
    ·
      refine ⟨37826855766197382009260227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50435807688263176012346969 37826855766197382009260227)
      ·
        refine ⟨56740283649296073013890341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37826855766197382009260227 56740283649296073013890341)
        ·
          refine ⟨10638803184243013690104439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56740283649296073013890341 10638803184243013690104439)
          ·
            refine ⟨15958204776364520535156659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10638803184243013690104439 15958204776364520535156659)
            ·
              refine ⟨23937307164546780802734989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15958204776364520535156659 23937307164546780802734989)
              ·
                refine ⟨8976490186705042801025621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23937307164546780802734989 8976490186705042801025621)
                ·
                  refine ⟨105193244375449720324519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8976490186705042801025621 105193244375449720324519)
                  ·
                    rfl

theorem cell23_1843768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 8].length) (baseStart_1843768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1843768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1843768 prefixEnd_1843768 := by exact prefixLift 1843768
  have htrace : WordTrace (prefixWord ++ tailWord_1843768) baseStart_1843768 baseEnd_1843768 := by
    simpa [prefixWord, tailWord_1843768, baseEnd_1843768] using wordTrace_append hprefix tailTrace_1843768
  have hstable : (prefixWord ++ tailWord_1843768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843768).length < 2 ^ (prefixWord ++ tailWord_1843768).sum := by decide
  have hdescent : baseEnd_1843768 < baseStart_1843768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843772 : List Nat := [2, 2, 2, 2, 3, 1, 3, 1, 3, 4]
def baseStart_1843772 : Nat := 118140960795 + 1843772 * 2 ^ 59
def prefixEnd_1843772 : Nat := 4983230072969 + 3 ^ 40 * 1843772 * 2
def baseEnd_1843772 : Nat := 315580417767221822423551

theorem tailTrace_1843772 : CollatzResearch.WordTrace tailWord_1843772 prefixEnd_1843772 315580417767221822423551 := by
  unfold tailWord_1843772
  simp only [CollatzResearch.WordTrace]
  refine ⟨33623944738168205016470785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44831926317557606688627713 33623944738168205016470785)
  ·
    refine ⟨25217958553626153762353089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33623944738168205016470785 25217958553626153762353089)
    ·
      refine ⟨18913468915219615321764817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25217958553626153762353089 18913468915219615321764817)
      ·
        refine ⟨14185101686414711491323613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18913468915219615321764817 14185101686414711491323613)
        ·
          refine ⟨5319413132405516809246355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14185101686414711491323613 5319413132405516809246355)
          ·
            refine ⟨7979119698608275213869533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5319413132405516809246355 7979119698608275213869533)
            ·
              refine ⟨2992169886978103205201075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7979119698608275213869533 2992169886978103205201075)
              ·
                refine ⟨4488254830467154807801613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2992169886978103205201075 4488254830467154807801613)
                ·
                  refine ⟨1683095561425183052925605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4488254830467154807801613 1683095561425183052925605)
                  ·
                    refine ⟨315580417767221822423551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1683095561425183052925605 315580417767221822423551)
                    ·
                      rfl

theorem cell23_1843772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 1, 3, 4].length) (baseStart_1843772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1843772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1843772 prefixEnd_1843772 := by exact prefixLift 1843772
  have htrace : WordTrace (prefixWord ++ tailWord_1843772) baseStart_1843772 baseEnd_1843772 := by
    simpa [prefixWord, tailWord_1843772, baseEnd_1843772] using wordTrace_append hprefix tailTrace_1843772
  have hstable : (prefixWord ++ tailWord_1843772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843772).length < 2 ^ (prefixWord ++ tailWord_1843772).sum := by decide
  have hdescent : baseEnd_1843772 < baseStart_1843772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843845 : List Nat := [1, 3, 1, 1, 4, 2, 1, 3, 1, 6]
def baseStart_1843845 : Nat := 118140960795 + 1843845 * 2 ^ 59
def prefixEnd_1843845 : Nat := 4983230072969 + 3 ^ 40 * 1843845 * 2
def baseEnd_1843845 : Nat := 315592912463147893885939

theorem tailTrace_1843845 : CollatzResearch.WordTrace tailWord_1843845 prefixEnd_1843845 315592912463147893885939 := by
  unfold tailWord_1843845
  simp only [CollatzResearch.WordTrace]
  refine ⟨67250552005071943500348989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44833701336714629000232659 67250552005071943500348989)
  ·
    refine ⟨25218957001901978812630871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67250552005071943500348989 25218957001901978812630871)
    ·
      refine ⟨37828435502852968218946307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25218957001901978812630871 37828435502852968218946307)
      ·
        refine ⟨56742653254279452328419461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37828435502852968218946307 56742653254279452328419461)
        ·
          refine ⟨10639247485177397311578649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56742653254279452328419461 10639247485177397311578649)
          ·
            refine ⟨7979435613883047983683987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10639247485177397311578649 7979435613883047983683987)
            ·
              refine ⟨11969153420824571975525981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7979435613883047983683987 11969153420824571975525981)
              ·
                refine ⟨4488432532809214490822243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11969153420824571975525981 4488432532809214490822243)
                ·
                  refine ⟨6732648799213821736233365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4488432532809214490822243 6732648799213821736233365)
                  ·
                    refine ⟨315592912463147893885939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6732648799213821736233365 315592912463147893885939)
                    ·
                      rfl

theorem cell23_1843845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3, 1, 6].length) (baseStart_1843845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1843845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1843845 prefixEnd_1843845 := by exact prefixLift 1843845
  have htrace : WordTrace (prefixWord ++ tailWord_1843845) baseStart_1843845 baseEnd_1843845 := by
    simpa [prefixWord, tailWord_1843845, baseEnd_1843845] using wordTrace_append hprefix tailTrace_1843845
  have hstable : (prefixWord ++ tailWord_1843845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843845).length < 2 ^ (prefixWord ++ tailWord_1843845).sum := by decide
  have hdescent : baseEnd_1843845 < baseStart_1843845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843865 : List Nat := [1, 2, 1, 2, 1, 2, 3, 4, 1, 2, 4]
def baseStart_1843865 : Nat := 118140960795 + 1843865 * 2 ^ 59
def prefixEnd_1843865 : Nat := 4983230072969 + 3 ^ 40 * 1843865 * 2
def baseEnd_1843865 : Nat := 946789007002533603407725

theorem tailTrace_1843865 : CollatzResearch.WordTrace tailWord_1843865 prefixEnd_1843865 946789007002533603407725 := by
  unfold tailWord_1843865
  simp only [CollatzResearch.WordTrace]
  refine ⟨67251281464999486916077049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44834187643332991277384699 67251281464999486916077049)
  ·
    refine ⟨50438461098749615187057787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67251281464999486916077049 50438461098749615187057787)
    ·
      refine ⟨75657691648124422780586681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50438461098749615187057787 75657691648124422780586681)
      ·
        refine ⟨56743268736093317085440011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75657691648124422780586681 56743268736093317085440011)
        ·
          refine ⟨85114903104139975628160017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56743268736093317085440011 85114903104139975628160017)
          ·
            refine ⟨63836177328104981721120013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85114903104139975628160017 63836177328104981721120013)
            ·
              refine ⟨23938566498039368145420005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63836177328104981721120013 23938566498039368145420005)
              ·
                refine ⟨4488481218382381527266251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23938566498039368145420005 4488481218382381527266251)
                ·
                  refine ⟨6732721827573572290899377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4488481218382381527266251 6732721827573572290899377)
                  ·
                    refine ⟨5049541370680179218174533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6732721827573572290899377 5049541370680179218174533)
                    ·
                      refine ⟨946789007002533603407725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5049541370680179218174533 946789007002533603407725)
                      ·
                        rfl

theorem cell23_1843865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4, 1, 2, 4].length) (baseStart_1843865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1843865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1843865 prefixEnd_1843865 := by exact prefixLift 1843865
  have htrace : WordTrace (prefixWord ++ tailWord_1843865) baseStart_1843865 baseEnd_1843865 := by
    simpa [prefixWord, tailWord_1843865, baseEnd_1843865] using wordTrace_append hprefix tailTrace_1843865
  have hstable : (prefixWord ++ tailWord_1843865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843865).length < 2 ^ (prefixWord ++ tailWord_1843865).sum := by decide
  have hdescent : baseEnd_1843865 < baseStart_1843865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843869 : List Nat := [1, 4, 2, 1, 1, 1, 6, 1, 1, 1, 4]
def baseStart_1843869 : Nat := 118140960795 + 1843869 * 2 ^ 59
def prefixEnd_1843869 : Nat := 4983230072969 + 3 ^ 40 * 1843869 * 2
def baseEnd_1843869 : Nat := 946791060925151587757707

theorem tailTrace_1843869 : CollatzResearch.WordTrace tailWord_1843869 prefixEnd_1843869 946791060925151587757707 := by
  unfold tailWord_1843869
  simp only [CollatzResearch.WordTrace]
  refine ⟨67251427356984995599222661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44834284904656663732815107 67251427356984995599222661)
  ·
    refine ⟨12609642629434686674854249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67251427356984995599222661 12609642629434686674854249)
    ·
      refine ⟨9457231972076015006140687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12609642629434686674854249 9457231972076015006140687)
      ·
        refine ⟨14185847958114022509211031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9457231972076015006140687 14185847958114022509211031)
        ·
          refine ⟨21278771937171033763816547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14185847958114022509211031 21278771937171033763816547)
          ·
            refine ⟨31918157905756550645724821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21278771937171033763816547 31918157905756550645724821)
            ·
              refine ⟨1496163651832338311518351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31918157905756550645724821 1496163651832338311518351)
              ·
                refine ⟨2244245477748507467277527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1496163651832338311518351 2244245477748507467277527)
                ·
                  refine ⟨3366368216622761200916291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2244245477748507467277527 3366368216622761200916291)
                  ·
                    refine ⟨5049552324934141801374437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3366368216622761200916291 5049552324934141801374437)
                    ·
                      refine ⟨946791060925151587757707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5049552324934141801374437 946791060925151587757707)
                      ·
                        rfl

theorem cell23_1843869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 1, 1, 1, 4].length) (baseStart_1843869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1843869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1843869 prefixEnd_1843869 := by exact prefixLift 1843869
  have htrace : WordTrace (prefixWord ++ tailWord_1843869) baseStart_1843869 baseEnd_1843869 := by
    simpa [prefixWord, tailWord_1843869, baseEnd_1843869] using wordTrace_append hprefix tailTrace_1843869
  have hstable : (prefixWord ++ tailWord_1843869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843869).length < 2 ^ (prefixWord ++ tailWord_1843869).sum := by decide
  have hdescent : baseEnd_1843869 < baseStart_1843869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843889 : List Nat := [1, 2, 2, 6, 1, 1, 1, 2, 1, 1, 5]
def baseStart_1843889 : Nat := 118140960795 + 1843889 * 2 ^ 59
def prefixEnd_1843889 : Nat := 4983230072969 + 3 ^ 40 * 1843889 * 2
def baseEnd_1843889 : Nat := 946801330538241509507615

theorem tailTrace_1843889 : CollatzResearch.WordTrace tailWord_1843889 prefixEnd_1843889 946801330538241509507615 := by
  unfold tailWord_1843889
  simp only [CollatzResearch.WordTrace]
  refine ⟨67252156816912539014950721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44834771211275026009967147 67252156816912539014950721)
  ·
    refine ⟨50439117612684404261213041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67252156816912539014950721 50439117612684404261213041)
    ·
      refine ⟨37829338209513303195909781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50439117612684404261213041 37829338209513303195909781)
      ·
        refine ⟨1773250228570936087308271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 37829338209513303195909781 1773250228570936087308271)
        ·
          refine ⟨2659875342856404130962407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1773250228570936087308271 2659875342856404130962407)
          ·
            refine ⟨3989813014284606196443611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2659875342856404130962407 3989813014284606196443611)
            ·
              refine ⟨5984719521426909294665417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3989813014284606196443611 5984719521426909294665417)
              ·
                refine ⟨4488539641070181970999063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5984719521426909294665417 4488539641070181970999063)
                ·
                  refine ⟨6732809461605272956498595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4488539641070181970999063 6732809461605272956498595)
                  ·
                    refine ⟨10099214192407909434747893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6732809461605272956498595 10099214192407909434747893)
                    ·
                      refine ⟨946801330538241509507615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10099214192407909434747893 946801330538241509507615)
                      ·
                        rfl

theorem cell23_1843889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_1843889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1843889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1843889 prefixEnd_1843889 := by exact prefixLift 1843889
  have htrace : WordTrace (prefixWord ++ tailWord_1843889) baseStart_1843889 baseEnd_1843889 := by
    simpa [prefixWord, tailWord_1843889, baseEnd_1843889] using wordTrace_append hprefix tailTrace_1843889
  have hstable : (prefixWord ++ tailWord_1843889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843889).length < 2 ^ (prefixWord ++ tailWord_1843889).sum := by decide
  have hdescent : baseEnd_1843889 < baseStart_1843889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843929 : List Nat := [1, 2, 1, 2, 3, 2, 1, 5, 1, 3, 2]
def baseStart_1843929 : Nat := 118140960795 + 1843929 * 2 ^ 59
def prefixEnd_1843929 : Nat := 4983230072969 + 3 ^ 40 * 1843929 * 2
def baseEnd_1843929 : Nat := 946821869764421353007431

theorem tailTrace_1843929 : CollatzResearch.WordTrace tailWord_1843929 prefixEnd_1843929 946821869764421353007431 := by
  unfold tailWord_1843929
  simp only [CollatzResearch.WordTrace]
  refine ⟨67253615736767625846406841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44835743824511750564271227 67253615736767625846406841)
  ·
    refine ⟨50440211802575719384805131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67253615736767625846406841 50440211802575719384805131)
    ·
      refine ⟨75660317703863579077207697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50440211802575719384805131 75660317703863579077207697)
      ·
        refine ⟨56745238277897684307905773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75660317703863579077207697 56745238277897684307905773)
        ·
          refine ⟨21279464354211631615464665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56745238277897684307905773 21279464354211631615464665)
          ·
            refine ⟨15959598265658723711598499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21279464354211631615464665 15959598265658723711598499)
            ·
              refine ⟨23939397398488085567397749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15959598265658723711598499 23939397398488085567397749)
              ·
                refine ⟨2244318506108258021943539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23939397398488085567397749 2244318506108258021943539)
                ·
                  refine ⟨3366477759162387032915309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2244318506108258021943539 3366477759162387032915309)
                  ·
                    refine ⟨1262429159685895137343241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3366477759162387032915309 1262429159685895137343241)
                    ·
                      refine ⟨946821869764421353007431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1262429159685895137343241 946821869764421353007431)
                      ·
                        rfl

theorem cell23_1843929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 5, 1, 3, 2].length) (baseStart_1843929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1843929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1843929 prefixEnd_1843929 := by exact prefixLift 1843929
  have htrace : WordTrace (prefixWord ++ tailWord_1843929) baseStart_1843929 baseEnd_1843929 := by
    simpa [prefixWord, tailWord_1843929, baseEnd_1843929] using wordTrace_append hprefix tailTrace_1843929
  have hstable : (prefixWord ++ tailWord_1843929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843929).length < 2 ^ (prefixWord ++ tailWord_1843929).sum := by decide
  have hdescent : baseEnd_1843929 < baseStart_1843929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843955 : List Nat := [1, 1, 1, 2, 2, 3, 1, 3, 1, 4, 4]
def baseStart_1843955 : Nat := 118140960795 + 1843955 * 2 ^ 59
def prefixEnd_1843955 : Nat := 4983230072969 + 3 ^ 40 * 1843955 * 2
def baseEnd_1843955 : Nat := 946835220261438251282311

theorem tailTrace_1843955 : CollatzResearch.WordTrace tailWord_1843955 prefixEnd_1843955 946835220261438251282311 := by
  unfold tailWord_1843955
  simp only [CollatzResearch.WordTrace]
  refine ⟨67254564034673432286853319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44836376023115621524568879 67254564034673432286853319)
  ·
    refine ⟨100881846052010148430279979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67254564034673432286853319 100881846052010148430279979)
    ·
      refine ⟨151322769078015222645419969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100881846052010148430279979 151322769078015222645419969)
      ·
        refine ⟨113492076808511416984064977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151322769078015222645419969 113492076808511416984064977)
        ·
          refine ⟨85119057606383562738048733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113492076808511416984064977 85119057606383562738048733)
          ·
            refine ⟨31919646602393836026768275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85119057606383562738048733 31919646602393836026768275)
            ·
              refine ⟨47879469903590754040152413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31919646602393836026768275 47879469903590754040152413)
              ·
                refine ⟨17954801213846532765057155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47879469903590754040152413 17954801213846532765057155)
                ·
                  refine ⟨26932201820769799147585733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17954801213846532765057155 26932201820769799147585733)
                  ·
                    refine ⟨5049787841394337340172325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26932201820769799147585733 5049787841394337340172325)
                    ·
                      refine ⟨946835220261438251282311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5049787841394337340172325 946835220261438251282311)
                      ·
                        rfl

theorem cell23_1843955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 4, 4].length) (baseStart_1843955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1843955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1843955 prefixEnd_1843955 := by exact prefixLift 1843955
  have htrace : WordTrace (prefixWord ++ tailWord_1843955) baseStart_1843955 baseEnd_1843955 := by
    simpa [prefixWord, tailWord_1843955, baseEnd_1843955] using wordTrace_append hprefix tailTrace_1843955
  have hstable : (prefixWord ++ tailWord_1843955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843955).length < 2 ^ (prefixWord ++ tailWord_1843955).sum := by decide
  have hdescent : baseEnd_1843955 < baseStart_1843955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843957 : List Nat := [1, 3, 6, 1, 2, 1, 1, 2, 1, 2, 3]
def baseStart_1843957 : Nat := 118140960795 + 1843957 * 2 ^ 59
def prefixEnd_1843957 : Nat := 4983230072969 + 3 ^ 40 * 1843957 * 2
def baseEnd_1843957 : Nat := 946836247222747243457303

theorem tailTrace_1843957 : CollatzResearch.WordTrace tailWord_1843957 prefixEnd_1843957 946836247222747243457303 := by
  unfold tailWord_1843957
  simp only [CollatzResearch.WordTrace]
  refine ⟨67254636980666186628426125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44836424653777457752284083 67254636980666186628426125)
  ·
    refine ⟨25220488867749819985659797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67254636980666186628426125 25220488867749819985659797)
    ·
      refine ⟨1182210415675772811827803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 25220488867749819985659797 1182210415675772811827803)
      ·
        refine ⟨1773315623513659217741705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1182210415675772811827803 1773315623513659217741705)
        ·
          refine ⟨1329986717635244413306279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1773315623513659217741705 1329986717635244413306279)
          ·
            refine ⟨1994980076452866619959419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1329986717635244413306279 1994980076452866619959419)
            ·
              refine ⟨2992470114679299929939129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1994980076452866619959419 2992470114679299929939129)
              ·
                refine ⟨2244352586009474947454347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2992470114679299929939129 2244352586009474947454347)
                ·
                  refine ⟨3366528879014212421181521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2244352586009474947454347 3366528879014212421181521)
                  ·
                    refine ⟨2524896659260659315886141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3366528879014212421181521 2524896659260659315886141)
                    ·
                      refine ⟨946836247222747243457303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2524896659260659315886141 946836247222747243457303)
                      ·
                        rfl

theorem cell23_1843957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_1843957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1843957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1843957 prefixEnd_1843957 := by exact prefixLift 1843957
  have htrace : WordTrace (prefixWord ++ tailWord_1843957) baseStart_1843957 baseEnd_1843957 := by
    simpa [prefixWord, tailWord_1843957, baseEnd_1843957] using wordTrace_append hprefix tailTrace_1843957
  have hstable : (prefixWord ++ tailWord_1843957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843957).length < 2 ^ (prefixWord ++ tailWord_1843957).sum := by decide
  have hdescent : baseEnd_1843957 < baseStart_1843957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843965 : List Nat := [1, 4, 1, 1, 1, 1, 4, 1, 9]
def baseStart_1843965 : Nat := 118140960795 + 1843965 * 2 ^ 59
def prefixEnd_1843965 : Nat := 4983230072969 + 3 ^ 40 * 1843965 * 2
def baseEnd_1843965 : Nat := 105204483896442579128585

theorem tailTrace_1843965 : CollatzResearch.WordTrace tailWord_1843965 prefixEnd_1843965 105204483896442579128585 := by
  unfold tailWord_1843965
  simp only [CollatzResearch.WordTrace]
  refine ⟨67254928764637203994717349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44836619176424802663144899 67254928764637203994717349)
  ·
    refine ⟨12610299143369475749009503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67254928764637203994717349 12610299143369475749009503)
    ·
      refine ⟨18915448715054213623514255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12610299143369475749009503 18915448715054213623514255)
      ·
        refine ⟨28373173072581320435271383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18915448715054213623514255 28373173072581320435271383)
        ·
          refine ⟨42559759608871980652907075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28373173072581320435271383 42559759608871980652907075)
          ·
            refine ⟨63839639413307970979360613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42559759608871980652907075 63839639413307970979360613)
            ·
              refine ⟨11969932389995244558630115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63839639413307970979360613 11969932389995244558630115)
              ·
                refine ⟨17954898584992866837945173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11969932389995244558630115 17954898584992866837945173)
                ·
                  refine ⟨105204483896442579128585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 17954898584992866837945173 105204483896442579128585)
                  ·
                    rfl

theorem cell23_1843965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 9].length) (baseStart_1843965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1843965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1843965 prefixEnd_1843965 := by exact prefixLift 1843965
  have htrace : WordTrace (prefixWord ++ tailWord_1843965) baseStart_1843965 baseEnd_1843965 := by
    simpa [prefixWord, tailWord_1843965, baseEnd_1843965] using wordTrace_append hprefix tailTrace_1843965
  have hstable : (prefixWord ++ tailWord_1843965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843965).length < 2 ^ (prefixWord ++ tailWord_1843965).sum := by decide
  have hdescent : baseEnd_1843965 < baseStart_1843965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843992 : List Nat := [2, 1, 2, 3, 1, 1, 1, 4, 2, 3, 3]
def baseStart_1843992 : Nat := 118140960795 + 1843992 * 2 ^ 59
def prefixEnd_1843992 : Nat := 4983230072969 + 3 ^ 40 * 1843992 * 2
def baseEnd_1843992 : Nat := 946854219045654606519641

theorem tailTrace_1843992 : CollatzResearch.WordTrace tailWord_1843992 prefixEnd_1843992 946854219045654606519641 := by
  unfold tailWord_1843992
  simp only [CollatzResearch.WordTrace]
  refine ⟨33627956767769693802975115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44837275690359591737300153 33627956767769693802975115)
  ·
    refine ⟨50441935151654540704462673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33627956767769693802975115 50441935151654540704462673)
    ·
      refine ⟨37831451363740905528347005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50441935151654540704462673 37831451363740905528347005)
      ·
        refine ⟨14186794261402839573130127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37831451363740905528347005 14186794261402839573130127)
        ·
          refine ⟨21280191392104259359695191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14186794261402839573130127 21280191392104259359695191)
          ·
            refine ⟨31920287088156389039542787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21280191392104259359695191 31920287088156389039542787)
            ·
              refine ⟨47880430632234583559314181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31920287088156389039542787 47880430632234583559314181)
              ·
                refine ⟨8977580743543984417371409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47880430632234583559314181 8977580743543984417371409)
                ·
                  refine ⟨6733185557657988313028557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8977580743543984417371409 6733185557657988313028557)
                  ·
                    refine ⟨2524944584121745617385709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6733185557657988313028557 2524944584121745617385709)
                    ·
                      refine ⟨946854219045654606519641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2524944584121745617385709 946854219045654606519641)
                      ·
                        rfl

theorem cell23_1843992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_1843992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1843992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1843992 prefixEnd_1843992 := by exact prefixLift 1843992
  have htrace : WordTrace (prefixWord ++ tailWord_1843992) baseStart_1843992 baseEnd_1843992 := by
    simpa [prefixWord, tailWord_1843992, baseEnd_1843992] using wordTrace_append hprefix tailTrace_1843992
  have hstable : (prefixWord ++ tailWord_1843992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843992).length < 2 ^ (prefixWord ++ tailWord_1843992).sum := by decide
  have hdescent : baseEnd_1843992 < baseStart_1843992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843999 : List Nat := [1, 1, 2, 4, 2, 3, 1, 4, 5]
def baseStart_1843999 : Nat := 118140960795 + 1843999 * 2 ^ 59
def prefixEnd_1843999 : Nat := 4983230072969 + 3 ^ 40 * 1843999 * 2
def baseEnd_1843999 : Nat := 105206423712248453236901

theorem tailTrace_1843999 : CollatzResearch.WordTrace tailWord_1843999 prefixEnd_1843999 105206423712248453236901 := by
  unfold tailWord_1843999
  simp only [CollatzResearch.WordTrace]
  refine ⟨67256168846514027801455051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44837445897676018534303367 67256168846514027801455051)
  ·
    refine ⟨100884253269771041702182577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67256168846514027801455051 100884253269771041702182577)
    ·
      refine ⟨75663189952328281276636933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100884253269771041702182577 75663189952328281276636933)
      ·
        refine ⟨14186848116061552739369425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75663189952328281276636933 14186848116061552739369425)
        ·
          refine ⟨10640136087046164554527069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14186848116061552739369425 10640136087046164554527069)
          ·
            refine ⟨3990051032642311707947651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10640136087046164554527069 3990051032642311707947651)
            ·
              refine ⟨5985076548963467561921477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3990051032642311707947651 5985076548963467561921477)
              ·
                refine ⟨1122201852930650167860277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5985076548963467561921477 1122201852930650167860277)
                ·
                  refine ⟨105206423712248453236901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1122201852930650167860277 105206423712248453236901)
                  ·
                    rfl

theorem cell23_1843999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 4, 5].length) (baseStart_1843999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1843999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1843999 prefixEnd_1843999 := by exact prefixLift 1843999
  have htrace : WordTrace (prefixWord ++ tailWord_1843999) baseStart_1843999 baseEnd_1843999 := by
    simpa [prefixWord, tailWord_1843999, baseEnd_1843999] using wordTrace_append hprefix tailTrace_1843999
  have hstable : (prefixWord ++ tailWord_1843999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843999).length < 2 ^ (prefixWord ++ tailWord_1843999).sum := by decide
  have hdescent : baseEnd_1843999 < baseStart_1843999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844029 : List Nat := [1, 4, 1, 4, 2, 1, 1, 1, 1, 7]
def baseStart_1844029 : Nat := 118140960795 + 1844029 * 2 ^ 59
def prefixEnd_1844029 : Nat := 4983230072969 + 3 ^ 40 * 1844029 * 2
def baseEnd_1844029 : Nat := 315624405943290320585657

theorem tailTrace_1844029 : CollatzResearch.WordTrace tailWord_1844029 prefixEnd_1844029 315624405943290320585657 := by
  unfold tailWord_1844029
  simp only [CollatzResearch.WordTrace]
  refine ⟨67257263036405342925047141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44838175357603561950031427 67257263036405342925047141)
  ·
    refine ⟨12610736819326001798446339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67257263036405342925047141 12610736819326001798446339)
    ·
      refine ⟨18916105228989002697669509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12610736819326001798446339 18916105228989002697669509)
      ·
        refine ⟨3546769730435438005813033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18916105228989002697669509 3546769730435438005813033)
        ·
          refine ⟨2660077297826578504359775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3546769730435438005813033 2660077297826578504359775)
          ·
            refine ⟨3990115946739867756539663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2660077297826578504359775 3990115946739867756539663)
            ·
              refine ⟨5985173920109801634809495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3990115946739867756539663 5985173920109801634809495)
              ·
                refine ⟨8977760880164702452214243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5985173920109801634809495 8977760880164702452214243)
                ·
                  refine ⟨13466641320247053678321365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8977760880164702452214243 13466641320247053678321365)
                  ·
                    refine ⟨315624405943290320585657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13466641320247053678321365 315624405943290320585657)
                    ·
                      rfl

theorem cell23_1844029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 7].length) (baseStart_1844029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1844029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1844029 prefixEnd_1844029 := by exact prefixLift 1844029
  have htrace : WordTrace (prefixWord ++ tailWord_1844029) baseStart_1844029 baseEnd_1844029 := by
    simpa [prefixWord, tailWord_1844029, baseEnd_1844029] using wordTrace_append hprefix tailTrace_1844029
  have hstable : (prefixWord ++ tailWord_1844029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844029).length < 2 ^ (prefixWord ++ tailWord_1844029).sum := by decide
  have hdescent : baseEnd_1844029 < baseStart_1844029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844033 : List Nat := [1, 2, 5, 3, 1, 1, 2, 3, 5]
def baseStart_1844033 : Nat := 118140960795 + 1844033 * 2 ^ 59
def prefixEnd_1844033 : Nat := 4983230072969 + 3 ^ 40 * 1844033 * 2
def baseEnd_1844033 : Nat := 105208363528054327345217

theorem tailTrace_1844033 : CollatzResearch.WordTrace tailWord_1844033 prefixEnd_1844033 105208363528054327345217 := by
  unfold tailWord_1844033
  simp only [CollatzResearch.WordTrace]
  refine ⟨67257408928390851608192753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44838272618927234405461835 67257408928390851608192753)
  ·
    refine ⟨50443056696293138706144565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67257408928390851608192753 50443056696293138706144565)
    ·
      refine ⟨4729036565277481753701053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50443056696293138706144565 4729036565277481753701053)
      ·
        refine ⟨1773388711979055657637895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4729036565277481753701053 1773388711979055657637895)
        ·
          refine ⟨2660083067968583486456843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1773388711979055657637895 2660083067968583486456843)
          ·
            refine ⟨3990124601952875229685265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2660083067968583486456843 3990124601952875229685265)
            ·
              refine ⟨2992593451464656422263949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3990124601952875229685265 2992593451464656422263949)
              ·
                refine ⟨1122222544299246158348981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2992593451464656422263949 1122222544299246158348981)
                ·
                  refine ⟨105208363528054327345217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1122222544299246158348981 105208363528054327345217)
                  ·
                    rfl

theorem cell23_1844033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 3, 5].length) (baseStart_1844033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1844033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1844033 prefixEnd_1844033 := by exact prefixLift 1844033
  have htrace : WordTrace (prefixWord ++ tailWord_1844033) baseStart_1844033 baseEnd_1844033 := by
    simpa [prefixWord, tailWord_1844033, baseEnd_1844033] using wordTrace_append hprefix tailTrace_1844033
  have hstable : (prefixWord ++ tailWord_1844033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844033).length < 2 ^ (prefixWord ++ tailWord_1844033).sum := by decide
  have hdescent : baseEnd_1844033 < baseStart_1844033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844086 : List Nat := [5, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3]
def baseStart_1844086 : Nat := 118140960795 + 1844086 * 2 ^ 59
def prefixEnd_1844086 : Nat := 4983230072969 + 3 ^ 40 * 1844086 * 2
def baseEnd_1844086 : Nat := 946902486227177238744209

theorem tailTrace_1844086 : CollatzResearch.WordTrace tailWord_1844086 prefixEnd_1844086 946902486227177238744209 := by
  unfold tailWord_1844086
  simp only [CollatzResearch.WordTrace]
  refine ⟨4203708874824927603742007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44839561331465894439914741 4203708874824927603742007)
  ·
    refine ⟨6305563312237391405613011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4203708874824927603742007 6305563312237391405613011)
    ·
      refine ⟨9458344968356087108419517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6305563312237391405613011 9458344968356087108419517)
      ·
        refine ⟨3546879363133532665657319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9458344968356087108419517 3546879363133532665657319)
        ·
          refine ⟨5320319044700298998485979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3546879363133532665657319 5320319044700298998485979)
          ·
            refine ⟨7980478567050448497728969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5320319044700298998485979 7980478567050448497728969)
            ·
              refine ⟨5985358925287836373296727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7980478567050448497728969 5985358925287836373296727)
              ·
                refine ⟨8978038387931754559945091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5985358925287836373296727 8978038387931754559945091)
                ·
                  refine ⟨13467057581897631839917637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8978038387931754559945091 13467057581897631839917637)
                  ·
                    refine ⟨2525073296605805969984557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13467057581897631839917637 2525073296605805969984557)
                    ·
                      refine ⟨946902486227177238744209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2525073296605805969984557 946902486227177238744209)
                      ·
                        rfl

theorem cell23_1844086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_1844086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1844086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1844086 prefixEnd_1844086 := by exact prefixLift 1844086
  have htrace : WordTrace (prefixWord ++ tailWord_1844086) baseStart_1844086 baseEnd_1844086 := by
    simpa [prefixWord, tailWord_1844086, baseEnd_1844086] using wordTrace_append hprefix tailTrace_1844086
  have hstable : (prefixWord ++ tailWord_1844086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844086).length < 2 ^ (prefixWord ++ tailWord_1844086).sum := by decide
  have hdescent : baseEnd_1844086 < baseStart_1844086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844149 : List Nat := [1, 3, 3, 2, 1, 1, 3, 2, 1, 6]
def baseStart_1844149 : Nat := 118140960795 + 1844149 * 2 ^ 59
def prefixEnd_1844149 : Nat := 4983230072969 + 3 ^ 40 * 1844149 * 2
def baseEnd_1844149 : Nat := 315644945169470164085473

theorem tailTrace_1844149 : CollatzResearch.WordTrace tailWord_1844149 prefixEnd_1844149 315644945169470164085473 := by
  unfold tailWord_1844149
  simp only [CollatzResearch.WordTrace]
  refine ⟨67261639795970603419415501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44841093197313735612943667 67261639795970603419415501)
  ·
    refine ⟨25223114923488976282280813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67261639795970603419415501 25223114923488976282280813)
    ·
      refine ⟨9458668096308366105855305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25223114923488976282280813 9458668096308366105855305)
      ·
        refine ⟨7094001072231274579391479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9458668096308366105855305 7094001072231274579391479)
        ·
          refine ⟨10641001608346911869087219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7094001072231274579391479 10641001608346911869087219)
          ·
            refine ⟨15961502412520367803630829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10641001608346911869087219 15961502412520367803630829)
            ·
              refine ⟨5985563404695137926361561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15961502412520367803630829 5985563404695137926361561)
              ·
                refine ⟨4489172553521353444771171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5985563404695137926361561 4489172553521353444771171)
                ·
                  refine ⟨6733758830282030167156757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4489172553521353444771171 6733758830282030167156757)
                  ·
                    refine ⟨315644945169470164085473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6733758830282030167156757 315644945169470164085473)
                    ·
                      rfl

theorem cell23_1844149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_1844149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1844149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1844149 prefixEnd_1844149 := by exact prefixLift 1844149
  have htrace : WordTrace (prefixWord ++ tailWord_1844149) baseStart_1844149 baseEnd_1844149 := by
    simpa [prefixWord, tailWord_1844149, baseEnd_1844149] using wordTrace_append hprefix tailTrace_1844149
  have hstable : (prefixWord ++ tailWord_1844149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844149).length < 2 ^ (prefixWord ++ tailWord_1844149).sum := by decide
  have hdescent : baseEnd_1844149 < baseStart_1844149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844186 : List Nat := [3, 1, 1, 2, 4, 2, 2, 1, 1, 2, 4]
def baseStart_1844186 : Nat := 118140960795 + 1844186 * 2 ^ 59
def prefixEnd_1844186 : Nat := 4983230072969 + 3 ^ 40 * 1844186 * 2
def baseEnd_1844186 : Nat := 946953834292626847493749

theorem tailTrace_1844186 : CollatzResearch.WordTrace tailWord_1844186 prefixEnd_1844186 946953834292626847493749 := by
  unfold tailWord_1844186
  simp only [CollatzResearch.WordTrace]
  refine ⟨16815747324209139684628103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44841992864557705825674941 16815747324209139684628103)
  ·
    refine ⟨25223620986313709526942155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16815747324209139684628103 25223620986313709526942155)
    ·
      refine ⟨37835431479470564290413233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25223620986313709526942155 37835431479470564290413233)
      ·
        refine ⟨28376573609602923217809925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37835431479470564290413233 28376573609602923217809925)
        ·
          refine ⟨5320607551800548103339361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28376573609602923217809925 5320607551800548103339361)
          ·
            refine ⟨3990455663850411077504521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5320607551800548103339361 3990455663850411077504521)
            ·
              refine ⟨2992841747887808308128391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3990455663850411077504521 2992841747887808308128391)
              ·
                refine ⟨4489262621831712462192587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2992841747887808308128391 4489262621831712462192587)
                ·
                  refine ⟨6733893932747568693288881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4489262621831712462192587 6733893932747568693288881)
                  ·
                    refine ⟨5050420449560676519966661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6733893932747568693288881 5050420449560676519966661)
                    ·
                      refine ⟨946953834292626847493749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5050420449560676519966661 946953834292626847493749)
                      ·
                        rfl

theorem cell23_1844186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 1, 1, 2, 4].length) (baseStart_1844186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1844186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1844186 prefixEnd_1844186 := by exact prefixLift 1844186
  have htrace : WordTrace (prefixWord ++ tailWord_1844186) baseStart_1844186 baseEnd_1844186 := by
    simpa [prefixWord, tailWord_1844186, baseEnd_1844186] using wordTrace_append hprefix tailTrace_1844186
  have hstable : (prefixWord ++ tailWord_1844186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844186).length < 2 ^ (prefixWord ++ tailWord_1844186).sum := by decide
  have hdescent : baseEnd_1844186 < baseStart_1844186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844210 : List Nat := [3, 2, 1, 5, 1, 1, 1, 3, 1, 2, 3]
def baseStart_1844210 : Nat := 118140960795 + 1844210 * 2 ^ 59
def prefixEnd_1844210 : Nat := 4983230072969 + 3 ^ 40 * 1844210 * 2
def baseEnd_1844210 : Nat := 946966157828334753593639

theorem tailTrace_1844210 : CollatzResearch.WordTrace tailWord_1844210 prefixEnd_1844210 946966157828334753593639 := by
  unfold tailWord_1844210
  simp only [CollatzResearch.WordTrace]
  refine ⟨16815966162187402709346521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44842576432499740558257389 16815966162187402709346521)
  ·
    refine ⟨12611974621640552032009891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16815966162187402709346521 12611974621640552032009891)
    ·
      refine ⟨18917961932460828048014837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12611974621640552032009891 18917961932460828048014837)
      ·
        refine ⟨1773558931168202629501391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18917961932460828048014837 1773558931168202629501391)
        ·
          refine ⟨2660338396752303944252087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1773558931168202629501391 2660338396752303944252087)
          ·
            refine ⟨3990507595128455916378131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2660338396752303944252087 3990507595128455916378131)
            ·
              refine ⟨5985761392692683874567197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3990507595128455916378131 5985761392692683874567197)
              ·
                refine ⟨2244660522259756452962699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5985761392692683874567197 2244660522259756452962699)
                ·
                  refine ⟨3366990783389634679444049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2244660522259756452962699 3366990783389634679444049)
                  ·
                    refine ⟨2525243087542226009583037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3366990783389634679444049 2525243087542226009583037)
                    ·
                      refine ⟨946966157828334753593639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2525243087542226009583037 946966157828334753593639)
                      ·
                        rfl

theorem cell23_1844210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_1844210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1844210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1844210 prefixEnd_1844210 := by exact prefixLift 1844210
  have htrace : WordTrace (prefixWord ++ tailWord_1844210) baseStart_1844210 baseEnd_1844210 := by
    simpa [prefixWord, tailWord_1844210, baseEnd_1844210] using wordTrace_append hprefix tailTrace_1844210
  have hstable : (prefixWord ++ tailWord_1844210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844210).length < 2 ^ (prefixWord ++ tailWord_1844210).sum := by decide
  have hdescent : baseEnd_1844210 < baseStart_1844210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844249 : List Nat := [1, 2, 1, 2, 1, 1, 4, 2, 2, 4, 3]
def baseStart_1844249 : Nat := 118140960795 + 1844249 * 2 ^ 59
def prefixEnd_1844249 : Nat := 4983230072969 + 3 ^ 40 * 1844249 * 2
def baseEnd_1844249 : Nat := 946986183573860101005959

theorem tailTrace_1844249 : CollatzResearch.WordTrace tailWord_1844249 prefixEnd_1844249 946986183573860101005959 := by
  unfold tailWord_1844249
  simp only [CollatzResearch.WordTrace]
  refine ⟨67265287095608320498055801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44843524730405546998703867 67265287095608320498055801)
  ·
    refine ⟨50448965321706240373541851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67265287095608320498055801 50448965321706240373541851)
    ·
      refine ⟨75673447982559360560312777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50448965321706240373541851 75673447982559360560312777)
      ·
        refine ⟨56755085986919520420234583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75673447982559360560312777 56755085986919520420234583)
        ·
          refine ⟨85132628980379280630351875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56755085986919520420234583 85132628980379280630351875)
          ·
            refine ⟨127698943470568920945527813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85132628980379280630351875 127698943470568920945527813)
            ·
              refine ⟨23943551900731672677286465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127698943470568920945527813 23943551900731672677286465)
              ·
                refine ⟨17957663925548754507964849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23943551900731672677286465 17957663925548754507964849)
                ·
                  refine ⟨13468247944161565880973637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17957663925548754507964849 13468247944161565880973637)
                  ·
                    refine ⟨2525296489530293602682557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13468247944161565880973637 2525296489530293602682557)
                    ·
                      refine ⟨946986183573860101005959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2525296489530293602682557 946986183573860101005959)
                      ·
                        rfl

theorem cell23_1844249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 4, 3].length) (baseStart_1844249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1844249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1844249 prefixEnd_1844249 := by exact prefixLift 1844249
  have htrace : WordTrace (prefixWord ++ tailWord_1844249) baseStart_1844249 baseEnd_1844249 := by
    simpa [prefixWord, tailWord_1844249, baseEnd_1844249] using wordTrace_append hprefix tailTrace_1844249
  have hstable : (prefixWord ++ tailWord_1844249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844249).length < 2 ^ (prefixWord ++ tailWord_1844249).sum := by decide
  have hdescent : baseEnd_1844249 < baseStart_1844249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844309 : List Nat := [1, 3, 2, 2, 1, 2, 1, 2, 1, 1, 7]
def baseStart_1844309 : Nat := 118140960795 + 1844309 * 2 ^ 59
def prefixEnd_1844309 : Nat := 4983230072969 + 3 ^ 40 * 1844309 * 2
def baseEnd_1844309 : Nat := 947016992413129866255683

theorem tailTrace_1844309 : CollatzResearch.WordTrace tailWord_1844309 prefixEnd_1844309 947016992413129866255683 := by
  unfold tailWord_1844309
  simp only [CollatzResearch.WordTrace]
  refine ⟨67267475475390950745239981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44844983650260633830159987 67267475475390950745239981)
  ·
    refine ⟨25225303303271606529464993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67267475475390950745239981 25225303303271606529464993)
    ·
      refine ⟨18918977477453704897098745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25225303303271606529464993 18918977477453704897098745)
      ·
        refine ⟨14189233108090278672824059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18918977477453704897098745 14189233108090278672824059)
        ·
          refine ⟨21283849662135418009236089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14189233108090278672824059 21283849662135418009236089)
          ·
            refine ⟨15962887246601563506927067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21283849662135418009236089 15962887246601563506927067)
            ·
              refine ⟨23944330869902345260390601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15962887246601563506927067 23944330869902345260390601)
              ·
                refine ⟨17958248152426758945292951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23944330869902345260390601 17958248152426758945292951)
                ·
                  refine ⟨26937372228640138417939427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17958248152426758945292951 26937372228640138417939427)
                  ·
                    refine ⟨40406058342960207626909141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26937372228640138417939427 40406058342960207626909141)
                    ·
                      refine ⟨947016992413129866255683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 40406058342960207626909141 947016992413129866255683)
                      ·
                        rfl

theorem cell23_1844309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_1844309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1844309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1844309 prefixEnd_1844309 := by exact prefixLift 1844309
  have htrace : WordTrace (prefixWord ++ tailWord_1844309) baseStart_1844309 baseEnd_1844309 := by
    simpa [prefixWord, tailWord_1844309, baseEnd_1844309] using wordTrace_append hprefix tailTrace_1844309
  have hstable : (prefixWord ++ tailWord_1844309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844309).length < 2 ^ (prefixWord ++ tailWord_1844309).sum := by decide
  have hdescent : baseEnd_1844309 < baseStart_1844309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844336 : List Nat := [2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 4]
def baseStart_1844336 : Nat := 118140960795 + 1844336 * 2 ^ 59
def prefixEnd_1844336 : Nat := 4983230072969 + 3 ^ 40 * 1844336 * 2
def baseEnd_1844336 : Nat := 947030856390801260618059

theorem tailTrace_1844336 : CollatzResearch.WordTrace tailWord_1844336 prefixEnd_1844336 947030856390801260618059 := by
  unfold tailWord_1844336
  simp only [CollatzResearch.WordTrace]
  refine ⟨33634230123146567178236431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44845640164195422904315241 33634230123146567178236431)
  ·
    refine ⟨50451345184719850767354647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33634230123146567178236431 50451345184719850767354647)
    ·
      refine ⟨75677017777079776151031971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50451345184719850767354647 75677017777079776151031971)
      ·
        refine ⟨113515526665619664226547957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75677017777079776151031971 113515526665619664226547957)
        ·
          refine ⟨10642080624901843521238871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 113515526665619664226547957 10642080624901843521238871)
          ·
            refine ⟨15963120937352765281858307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10642080624901843521238871 15963120937352765281858307)
            ·
              refine ⟨23944681406029147922787461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15963120937352765281858307 23944681406029147922787461)
              ·
                refine ⟨4489627763630465235522649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23944681406029147922787461 4489627763630465235522649)
                ·
                  refine ⟨3367220822722848926641987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4489627763630465235522649 3367220822722848926641987)
                  ·
                    refine ⟨5050831234084273389962981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3367220822722848926641987 5050831234084273389962981)
                    ·
                      refine ⟨947030856390801260618059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5050831234084273389962981 947030856390801260618059)
                      ·
                        rfl

theorem cell23_1844336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 4].length) (baseStart_1844336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1844336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1844336 prefixEnd_1844336 := by exact prefixLift 1844336
  have htrace : WordTrace (prefixWord ++ tailWord_1844336) baseStart_1844336 baseEnd_1844336 := by
    simpa [prefixWord, tailWord_1844336, baseEnd_1844336] using wordTrace_append hprefix tailTrace_1844336
  have hstable : (prefixWord ++ tailWord_1844336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844336).length < 2 ^ (prefixWord ++ tailWord_1844336).sum := by decide
  have hdescent : baseEnd_1844336 < baseStart_1844336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844353 : List Nat := [1, 2, 4, 2, 2, 1, 1, 1, 1, 6, 2]
def baseStart_1844353 : Nat := 118140960795 + 1844353 * 2 ^ 59
def prefixEnd_1844353 : Nat := 4983230072969 + 3 ^ 40 * 1844353 * 2
def baseEnd_1844353 : Nat := 947039585561927694105481

theorem tailTrace_1844353 : CollatzResearch.WordTrace tailWord_1844353 prefixEnd_1844353 947039585561927694105481 := by
  unfold tailWord_1844353
  simp only [CollatzResearch.WordTrace]
  refine ⟨67269080287231546259841713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44846053524821030839894475 67269080287231546259841713)
  ·
    refine ⟨50451810215423659694881285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67269080287231546259841713 50451810215423659694881285)
    ·
      refine ⟨9459714415391936192790241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50451810215423659694881285 9459714415391936192790241)
      ·
        refine ⟨7094785811543952144592681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9459714415391936192790241 7094785811543952144592681)
        ·
          refine ⟨5321089358657964108444511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7094785811543952144592681 5321089358657964108444511)
          ·
            refine ⟨7981634037986946162666767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5321089358657964108444511 7981634037986946162666767)
            ·
              refine ⟨11972451056980419244000151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7981634037986946162666767 11972451056980419244000151)
              ·
                refine ⟨17958676585470628866000227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11972451056980419244000151 17958676585470628866000227)
                ·
                  refine ⟨26938014878205943299000341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17958676585470628866000227 26938014878205943299000341)
                  ·
                    refine ⟨1262719447415903592140641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26938014878205943299000341 1262719447415903592140641)
                    ·
                      refine ⟨947039585561927694105481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1262719447415903592140641 947039585561927694105481)
                      ·
                        rfl

theorem cell23_1844353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_1844353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1844353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1844353 prefixEnd_1844353 := by exact prefixLift 1844353
  have htrace : WordTrace (prefixWord ++ tailWord_1844353) baseStart_1844353 baseEnd_1844353 := by
    simpa [prefixWord, tailWord_1844353, baseEnd_1844353] using wordTrace_append hprefix tailTrace_1844353
  have hstable : (prefixWord ++ tailWord_1844353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844353).length < 2 ^ (prefixWord ++ tailWord_1844353).sum := by decide
  have hdescent : baseEnd_1844353 < baseStart_1844353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844359 : List Nat := [1, 1, 4, 2, 1, 1, 1, 2, 10]
def baseStart_1844359 : Nat := 118140960795 + 1844359 * 2 ^ 59
def prefixEnd_1844359 : Nat := 4983230072969 + 3 ^ 40 * 1844359 * 2
def baseEnd_1844359 : Nat := 105226962938428296736717

theorem tailTrace_1844359 : CollatzResearch.WordTrace tailWord_1844359 prefixEnd_1844359 105226962938428296736717 := by
  unfold tailWord_1844359
  simp only [CollatzResearch.WordTrace]
  refine ⟨67269299125209809284560131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44846199416806539523040087 67269299125209809284560131)
  ·
    refine ⟨100903948687814713926840197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67269299125209809284560131 100903948687814713926840197)
    ·
      refine ⟨18919490378965258861282537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100903948687814713926840197 18919490378965258861282537)
      ·
        refine ⟨14189617784223944145961903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18919490378965258861282537 14189617784223944145961903)
        ·
          refine ⟨21284426676335916218942855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14189617784223944145961903 21284426676335916218942855)
          ·
            refine ⟨31926640014503874328414283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21284426676335916218942855 31926640014503874328414283)
            ·
              refine ⟨47889960021755811492621425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31926640014503874328414283 47889960021755811492621425)
              ·
                refine ⟨35917470016316858619466069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47889960021755811492621425 35917470016316858619466069)
                ·
                  refine ⟨105226962938428296736717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 35917470016316858619466069 105226962938428296736717)
                  ·
                    rfl

theorem cell23_1844359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 10].length) (baseStart_1844359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1844359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1844359 prefixEnd_1844359 := by exact prefixLift 1844359
  have htrace : WordTrace (prefixWord ++ tailWord_1844359) baseStart_1844359 baseEnd_1844359 := by
    simpa [prefixWord, tailWord_1844359, baseEnd_1844359] using wordTrace_append hprefix tailTrace_1844359
  have hstable : (prefixWord ++ tailWord_1844359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844359).length < 2 ^ (prefixWord ++ tailWord_1844359).sum := by decide
  have hdescent : baseEnd_1844359 < baseStart_1844359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844370 : List Nat := [3, 2, 3, 1, 1, 4, 1, 1, 2, 1, 4]
def baseStart_1844370 : Nat := 118140960795 + 1844370 * 2 ^ 59
def prefixEnd_1844370 : Nat := 4983230072969 + 3 ^ 40 * 1844370 * 2
def baseEnd_1844370 : Nat := 947048314733054127592903

theorem tailTrace_1844370 : CollatzResearch.WordTrace tailWord_1844370 prefixEnd_1844370 947048314733054127592903 := by
  unfold tailWord_1844370
  simp only [CollatzResearch.WordTrace]
  refine ⟨16817425082042489540802641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44846466885446638775473709 16817425082042489540802641)
  ·
    refine ⟨12613068811531867155601981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16817425082042489540802641 12613068811531867155601981)
    ·
      refine ⟨4729900804324450183350743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12613068811531867155601981 4729900804324450183350743)
      ·
        refine ⟨7094851206486675275026115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4729900804324450183350743 7094851206486675275026115)
        ·
          refine ⟨10642276809730012912539173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7094851206486675275026115 10642276809730012912539173)
          ·
            refine ⟨1995426901824377421101095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10642276809730012912539173 1995426901824377421101095)
            ·
              refine ⟨2993140352736566131651643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1995426901824377421101095 2993140352736566131651643)
              ·
                refine ⟨4489710529104849197477465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2993140352736566131651643 4489710529104849197477465)
                ·
                  refine ⟨3367282896828636898108099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4489710529104849197477465 3367282896828636898108099)
                  ·
                    refine ⟨5050924345242955347162149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3367282896828636898108099 5050924345242955347162149)
                    ·
                      refine ⟨947048314733054127592903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5050924345242955347162149 947048314733054127592903)
                      ·
                        rfl

theorem cell23_1844370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_1844370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1844370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1844370 prefixEnd_1844370 := by exact prefixLift 1844370
  have htrace : WordTrace (prefixWord ++ tailWord_1844370) baseStart_1844370 baseEnd_1844370 := by
    simpa [prefixWord, tailWord_1844370, baseEnd_1844370] using wordTrace_append hprefix tailTrace_1844370
  have hstable : (prefixWord ++ tailWord_1844370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844370).length < 2 ^ (prefixWord ++ tailWord_1844370).sum := by decide
  have hdescent : baseEnd_1844370 < baseStart_1844370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844380 : List Nat := [2, 2, 3, 2, 1, 2, 1, 5, 1, 4]
def baseStart_1844380 : Nat := 118140960795 + 1844380 * 2 ^ 59
def prefixEnd_1844380 : Nat := 4983230072969 + 3 ^ 40 * 1844380 * 2
def baseEnd_1844380 : Nat := 315684483179866362822619

theorem tailTrace_1844380 : CollatzResearch.WordTrace tailWord_1844380 prefixEnd_1844380 315684483179866362822619 := by
  unfold tailWord_1844380
  simp only [CollatzResearch.WordTrace]
  refine ⟨33635032529066864935537297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44846710038755819914049729 33635032529066864935537297)
  ·
    refine ⟨25226274396800148701652973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33635032529066864935537297 25226274396800148701652973)
    ·
      refine ⟨9459852898800055763119865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25226274396800148701652973 9459852898800055763119865)
      ·
        refine ⟨7094889674100041822339899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9459852898800055763119865 7094889674100041822339899)
        ·
          refine ⟨10642334511150062733509849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7094889674100041822339899 10642334511150062733509849)
          ·
            refine ⟨7981750883362547050132387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10642334511150062733509849 7981750883362547050132387)
            ·
              refine ⟨11972626325043820575198581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7981750883362547050132387 11972626325043820575198581)
              ·
                refine ⟨1122433717972858178924867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11972626325043820575198581 1122433717972858178924867)
                ·
                  refine ⟨1683650576959287268387301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1122433717972858178924867 1683650576959287268387301)
                  ·
                    refine ⟨315684483179866362822619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1683650576959287268387301 315684483179866362822619)
                    ·
                      rfl

theorem cell23_1844380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 5, 1, 4].length) (baseStart_1844380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1844380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1844380 prefixEnd_1844380 := by exact prefixLift 1844380
  have htrace : WordTrace (prefixWord ++ tailWord_1844380) baseStart_1844380 baseEnd_1844380 := by
    simpa [prefixWord, tailWord_1844380, baseEnd_1844380] using wordTrace_append hprefix tailTrace_1844380
  have hstable : (prefixWord ++ tailWord_1844380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844380).length < 2 ^ (prefixWord ++ tailWord_1844380).sum := by decide
  have hdescent : baseEnd_1844380 < baseStart_1844380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844403 : List Nat := [1, 1, 1, 2, 3, 2, 3, 3, 3, 1, 3]
def baseStart_1844403 : Nat := 118140960795 + 1844403 * 2 ^ 59
def prefixEnd_1844403 : Nat := 4983230072969 + 3 ^ 40 * 1844403 * 2
def baseEnd_1844403 : Nat := 947065259594652498480251

theorem tailTrace_1844403 : CollatzResearch.WordTrace tailWord_1844403 prefixEnd_1844403 947065259594652498480251 := by
  unfold tailWord_1844403
  simp only [CollatzResearch.WordTrace]
  refine ⟨67270903937050404799161863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44847269291366936532774575 67270903937050404799161863)
  ·
    refine ⟨100906355905575607198742795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67270903937050404799161863 100906355905575607198742795)
    ·
      refine ⟨151359533858363410798114193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100906355905575607198742795 151359533858363410798114193)
      ·
        refine ⟨113519650393772558098585645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151359533858363410798114193 113519650393772558098585645)
        ·
          refine ⟨42569868897664709286969617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113519650393772558098585645 42569868897664709286969617)
          ·
            refine ⟨31927401673248531965227213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42569868897664709286969617 31927401673248531965227213)
            ·
              refine ⟨11972775627468199486960205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31927401673248531965227213 11972775627468199486960205)
              ·
                refine ⟨4489790860300574807610077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11972775627468199486960205 4489790860300574807610077)
                ·
                  refine ⟨1683671572612715552853779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4489790860300574807610077 1683671572612715552853779)
                  ·
                    refine ⟨2525507358919073329280669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1683671572612715552853779 2525507358919073329280669)
                    ·
                      refine ⟨947065259594652498480251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2525507358919073329280669 947065259594652498480251)
                      ·
                        rfl

theorem cell23_1844403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 3, 1, 3].length) (baseStart_1844403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1844403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1844403 prefixEnd_1844403 := by exact prefixLift 1844403
  have htrace : WordTrace (prefixWord ++ tailWord_1844403) baseStart_1844403 baseEnd_1844403 := by
    simpa [prefixWord, tailWord_1844403, baseEnd_1844403] using wordTrace_append hprefix tailTrace_1844403
  have hstable : (prefixWord ++ tailWord_1844403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844403).length < 2 ^ (prefixWord ++ tailWord_1844403).sum := by decide
  have hdescent : baseEnd_1844403 < baseStart_1844403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844413 : List Nat := [1, 4, 1, 2, 1, 1, 3, 2, 1, 5, 2]
def baseStart_1844413 : Nat := 118140960795 + 1844413 * 2 ^ 59
def prefixEnd_1844413 : Nat := 4983230072969 + 3 ^ 40 * 1844413 * 2
def baseEnd_1844413 : Nat := 947070394401197459355205

theorem tailTrace_1844413 : CollatzResearch.WordTrace tailWord_1844413 prefixEnd_1844413 947070394401197459355205 := by
  unfold tailWord_1844413
  simp only [CollatzResearch.WordTrace]
  refine ⟨67271268667014176507025893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44847512444676117671350595 67271268667014176507025893)
  ·
    refine ⟨12613362875065158095067355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67271268667014176507025893 12613362875065158095067355)
    ·
      refine ⟨18920044312597737142601033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12613362875065158095067355 18920044312597737142601033)
      ·
        refine ⟨14190033234448302856950775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18920044312597737142601033 14190033234448302856950775)
        ·
          refine ⟨21285049851672454285426163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14190033234448302856950775 21285049851672454285426163)
          ·
            refine ⟨31927574777508681428139245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21285049851672454285426163 31927574777508681428139245)
            ·
              refine ⟨11972840541565755535552217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31927574777508681428139245 11972840541565755535552217)
              ·
                refine ⟨8979630406174316651664163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11972840541565755535552217 8979630406174316651664163)
                ·
                  refine ⟨13469445609261474977496245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8979630406174316651664163 13469445609261474977496245)
                  ·
                    refine ⟨1262760525868263279140273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13469445609261474977496245 1262760525868263279140273)
                    ·
                      refine ⟨947070394401197459355205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1262760525868263279140273 947070394401197459355205)
                      ·
                        rfl

theorem cell23_1844413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 5, 2].length) (baseStart_1844413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1844413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1844413 prefixEnd_1844413 := by exact prefixLift 1844413
  have htrace : WordTrace (prefixWord ++ tailWord_1844413) baseStart_1844413 baseEnd_1844413 := by
    simpa [prefixWord, tailWord_1844413, baseEnd_1844413] using wordTrace_append hprefix tailTrace_1844413
  have hstable : (prefixWord ++ tailWord_1844413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844413).length < 2 ^ (prefixWord ++ tailWord_1844413).sum := by decide
  have hdescent : baseEnd_1844413 < baseStart_1844413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844456 : List Nat := [2, 1, 4, 1, 2, 1, 1, 1, 3, 1, 6]
def baseStart_1844456 : Nat := 118140960795 + 1844456 * 2 ^ 59
def prefixEnd_1844456 : Nat := 4983230072969 + 3 ^ 40 * 1844456 * 2
def baseEnd_1844456 : Nat := 947092474069340791117507

theorem tailTrace_1844456 : CollatzResearch.WordTrace tailWord_1844456 prefixEnd_1844456 947092474069340791117507 := by
  unfold tailWord_1844456
  simp only [CollatzResearch.WordTrace]
  refine ⟨33636418502929197425420611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44848558003905596567227481 33636418502929197425420611)
  ·
    refine ⟨50454627754393796138130917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33636418502929197425420611 50454627754393796138130917)
    ·
      refine ⟨9460242703948836775899547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50454627754393796138130917 9460242703948836775899547)
      ·
        refine ⟨14190364055923255163849321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9460242703948836775899547 14190364055923255163849321)
        ·
          refine ⟨10642773041942441372886991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14190364055923255163849321 10642773041942441372886991)
          ·
            refine ⟨15964159562913662059330487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10642773041942441372886991 15964159562913662059330487)
            ·
              refine ⟨23946239344370493088995731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15964159562913662059330487 23946239344370493088995731)
              ·
                refine ⟨35919359016555739633493597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23946239344370493088995731 35919359016555739633493597)
                ·
                  refine ⟨13469759631208402362560099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35919359016555739633493597 13469759631208402362560099)
                  ·
                    refine ⟨20204639446812603543840149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13469759631208402362560099 20204639446812603543840149)
                    ·
                      refine ⟨947092474069340791117507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20204639446812603543840149 947092474069340791117507)
                      ·
                        rfl

theorem cell23_1844456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_1844456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1844456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1844456 prefixEnd_1844456 := by exact prefixLift 1844456
  have htrace : WordTrace (prefixWord ++ tailWord_1844456) baseStart_1844456 baseEnd_1844456 := by
    simpa [prefixWord, tailWord_1844456, baseEnd_1844456] using wordTrace_append hprefix tailTrace_1844456
  have hstable : (prefixWord ++ tailWord_1844456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844456).length < 2 ^ (prefixWord ++ tailWord_1844456).sum := by decide
  have hdescent : baseEnd_1844456 < baseStart_1844456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844567 : List Nat := [1, 1, 3, 2, 3, 3, 1, 1, 4, 2, 2]
def baseStart_1844567 : Nat := 118140960795 + 1844567 * 2 ^ 59
def prefixEnd_1844567 : Nat := 4983230072969 + 3 ^ 40 * 1844567 * 2
def baseEnd_1844567 : Nat := 947149470421989856829497

theorem tailTrace_1844567 : CollatzResearch.WordTrace tailWord_1844567 prefixEnd_1844567 947149470421989856829497 := by
  unfold tailWord_1844567
  simp only [CollatzResearch.WordTrace]
  refine ⟨67276885508456260808131955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44851257005637507205421303 67276885508456260808131955)
  ·
    refine ⟨100915328262684391212197933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67276885508456260808131955 100915328262684391212197933)
    ·
      refine ⟨37843248098506646704574225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100915328262684391212197933 37843248098506646704574225)
      ·
        refine ⟨28382436073879985028430669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37843248098506646704574225 28382436073879985028430669)
        ·
          refine ⟨10643413527704994385661501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28382436073879985028430669 10643413527704994385661501)
          ·
            refine ⟨3991280072889372894623063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10643413527704994385661501 3991280072889372894623063)
            ·
              refine ⟨5986920109334059341934595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3991280072889372894623063 5986920109334059341934595)
              ·
                refine ⟨8980380164001089012901893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5986920109334059341934595 8980380164001089012901893)
                ·
                  refine ⟨1683821280750204189919105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8980380164001089012901893 1683821280750204189919105)
                  ·
                    refine ⟨1262865960562653142439329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1683821280750204189919105 1262865960562653142439329)
                    ·
                      refine ⟨947149470421989856829497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1262865960562653142439329 947149470421989856829497)
                      ·
                        rfl

theorem cell23_1844567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 4, 2, 2].length) (baseStart_1844567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1844567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1844567 prefixEnd_1844567 := by exact prefixLift 1844567
  have htrace : WordTrace (prefixWord ++ tailWord_1844567) baseStart_1844567 baseEnd_1844567 := by
    simpa [prefixWord, tailWord_1844567, baseEnd_1844567] using wordTrace_append hprefix tailTrace_1844567
  have hstable : (prefixWord ++ tailWord_1844567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844567).length < 2 ^ (prefixWord ++ tailWord_1844567).sum := by decide
  have hdescent : baseEnd_1844567 < baseStart_1844567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844584 : List Nat := [2, 1, 4, 2, 3, 2, 1, 1, 1, 4, 2]
def baseStart_1844584 : Nat := 118140960795 + 1844584 * 2 ^ 59
def prefixEnd_1844584 : Nat := 4983230072969 + 3 ^ 40 * 1844584 * 2
def baseEnd_1844584 : Nat := 947158199593116290316919

theorem tailTrace_1844584 : CollatzResearch.WordTrace tailWord_1844584 prefixEnd_1844584 947158199593116290316919 := by
  unfold tailWord_1844584
  simp only [CollatzResearch.WordTrace]
  refine ⟨33638752774697336355750403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44851670366263115141000537 33638752774697336355750403)
  ·
    refine ⟨50458129162046004533625605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33638752774697336355750403 50458129162046004533625605)
    ·
      refine ⟨9460899217883625850054801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50458129162046004533625605 9460899217883625850054801)
      ·
        refine ⟨7095674413412719387541101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9460899217883625850054801 7095674413412719387541101)
        ·
          refine ⟨2660877905029769770327913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7095674413412719387541101 2660877905029769770327913)
          ·
            refine ⟨1995658428772327327745935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2660877905029769770327913 1995658428772327327745935)
            ·
              refine ⟨2993487643158490991618903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1995658428772327327745935 2993487643158490991618903)
              ·
                refine ⟨4490231464737736487428355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2993487643158490991618903 4490231464737736487428355)
                ·
                  refine ⟨6735347197106604731142533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4490231464737736487428355 6735347197106604731142533)
                  ·
                    refine ⟨1262877599457488387089225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6735347197106604731142533 1262877599457488387089225)
                    ·
                      refine ⟨947158199593116290316919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1262877599457488387089225 947158199593116290316919)
                      ·
                        rfl

theorem cell23_1844584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_1844584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1844584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1844584 prefixEnd_1844584 := by exact prefixLift 1844584
  have htrace : WordTrace (prefixWord ++ tailWord_1844584) baseStart_1844584 baseEnd_1844584 := by
    simpa [prefixWord, tailWord_1844584, baseEnd_1844584] using wordTrace_append hprefix tailTrace_1844584
  have hstable : (prefixWord ++ tailWord_1844584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844584).length < 2 ^ (prefixWord ++ tailWord_1844584).sum := by decide
  have hdescent : baseEnd_1844584 < baseStart_1844584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844603 : List Nat := [1, 1, 1, 1, 1, 6, 2, 3, 2, 5]
def baseStart_1844603 : Nat := 118140960795 + 1844603 * 2 ^ 59
def prefixEnd_1844603 : Nat := 4983230072969 + 3 ^ 40 * 1844603 * 2
def baseEnd_1844603 : Nat := 315722651908517238659777

theorem tailTrace_1844603 : CollatzResearch.WordTrace tailWord_1844603 prefixEnd_1844603 315722651908517238659777 := by
  unfold tailWord_1844603
  simp only [CollatzResearch.WordTrace]
  refine ⟨67278198536325838956442463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44852132357550559304294975 67278198536325838956442463)
  ·
    refine ⟨100917297804488758434663695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67278198536325838956442463 100917297804488758434663695)
    ·
      refine ⟨151375946706733137651995543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100917297804488758434663695 151375946706733137651995543)
      ·
        refine ⟨227063920060099706477993315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151375946706733137651995543 227063920060099706477993315)
        ·
          refine ⟨340595880090149559716989973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227063920060099706477993315 340595880090149559716989973)
          ·
            refine ⟨15965431879225760611733905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 340595880090149559716989973 15965431879225760611733905)
            ·
              refine ⟨11974073909419320458800429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15965431879225760611733905 11974073909419320458800429)
              ·
                refine ⟨4490277716032245172050161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11974073909419320458800429 4490277716032245172050161)
                ·
                  refine ⟨3367708287024183879037621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4490277716032245172050161 3367708287024183879037621)
                  ·
                    refine ⟨315722651908517238659777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3367708287024183879037621 315722651908517238659777)
                    ·
                      rfl

theorem cell23_1844603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3, 2, 5].length) (baseStart_1844603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1844603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1844603 prefixEnd_1844603 := by exact prefixLift 1844603
  have htrace : WordTrace (prefixWord ++ tailWord_1844603) baseStart_1844603 baseEnd_1844603 := by
    simpa [prefixWord, tailWord_1844603, baseEnd_1844603] using wordTrace_append hprefix tailTrace_1844603
  have hstable : (prefixWord ++ tailWord_1844603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844603).length < 2 ^ (prefixWord ++ tailWord_1844603).sum := by decide
  have hdescent : baseEnd_1844603 < baseStart_1844603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844640 : List Nat := [2, 1, 1, 4, 1, 2, 2, 1, 1, 6, 2]
def baseStart_1844640 : Nat := 118140960795 + 1844640 * 2 ^ 59
def prefixEnd_1844640 : Nat := 4983230072969 + 3 ^ 40 * 1844640 * 2
def baseEnd_1844640 : Nat := 947186954509768071216661

theorem tailTrace_1844640 : CollatzResearch.WordTrace tailWord_1844640 prefixEnd_1844640 947186954509768071216661 := by
  unfold tailWord_1844640
  simp only [CollatzResearch.WordTrace]
  refine ⟨33639774018595897137769687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44853032024794529517026249 33639774018595897137769687)
  ·
    refine ⟨50459661027893845706654531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33639774018595897137769687 50459661027893845706654531)
    ·
      refine ⟨75689491541840768559981797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50459661027893845706654531 75689491541840768559981797)
      ·
        refine ⟨14191779664095144104996587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75689491541840768559981797 14191779664095144104996587)
        ·
          refine ⟨21287669496142716157494881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14191779664095144104996587 21287669496142716157494881)
          ·
            refine ⟨15965752122107037118121161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21287669496142716157494881 15965752122107037118121161)
            ·
              refine ⟨11974314091580277838590871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15965752122107037118121161 11974314091580277838590871)
              ·
                refine ⟨17961471137370416757886307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11974314091580277838590871 17961471137370416757886307)
                ·
                  refine ⟨26942206706055625136829461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17961471137370416757886307 26942206706055625136829461)
                  ·
                    refine ⟨1262915939346357428288881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26942206706055625136829461 1262915939346357428288881)
                    ·
                      refine ⟨947186954509768071216661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1262915939346357428288881 947186954509768071216661)
                      ·
                        rfl

theorem cell23_1844640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 1, 6, 2].length) (baseStart_1844640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1844640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1844640 prefixEnd_1844640 := by exact prefixLift 1844640
  have htrace : WordTrace (prefixWord ++ tailWord_1844640) baseStart_1844640 baseEnd_1844640 := by
    simpa [prefixWord, tailWord_1844640, baseEnd_1844640] using wordTrace_append hprefix tailTrace_1844640
  have hstable : (prefixWord ++ tailWord_1844640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844640).length < 2 ^ (prefixWord ++ tailWord_1844640).sum := by decide
  have hdescent : baseEnd_1844640 < baseStart_1844640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844680 : List Nat := [2, 1, 3, 1, 3, 1, 4, 2, 6]
def baseStart_1844680 : Nat := 118140960795 + 1844680 * 2 ^ 59
def prefixEnd_1844680 : Nat := 4983230072969 + 3 ^ 40 * 1844680 * 2
def baseEnd_1844680 : Nat := 105245277081771990524053

theorem tailTrace_1844680 : CollatzResearch.WordTrace tailWord_1844680 prefixEnd_1844680 105245277081771990524053 := by
  unfold tailWord_1844680
  simp only [CollatzResearch.WordTrace]
  refine ⟨33640503478523440553497747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44854004638031254071330329 33640503478523440553497747)
  ·
    refine ⟨50460755217785160830246621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33640503478523440553497747 50460755217785160830246621)
    ·
      refine ⟨18922783206669435311342483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50460755217785160830246621 18922783206669435311342483)
      ·
        refine ⟨28384174810004152967013725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18922783206669435311342483 28384174810004152967013725)
        ·
          refine ⟨10644065553751557362630147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28384174810004152967013725 10644065553751557362630147)
          ·
            refine ⟨15966098330627336043945221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10644065553751557362630147 15966098330627336043945221)
            ·
              refine ⟨2993643436992625508239729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15966098330627336043945221 2993643436992625508239729)
              ·
                refine ⟨2245232577744469131179797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2993643436992625508239729 2245232577744469131179797)
                ·
                  refine ⟨105245277081771990524053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2245232577744469131179797 105245277081771990524053)
                  ·
                    rfl

theorem cell23_1844680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 2, 6].length) (baseStart_1844680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1844680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1844680 prefixEnd_1844680 := by exact prefixLift 1844680
  have htrace : WordTrace (prefixWord ++ tailWord_1844680) baseStart_1844680 baseEnd_1844680 := by
    simpa [prefixWord, tailWord_1844680, baseEnd_1844680] using wordTrace_append hprefix tailTrace_1844680
  have hstable : (prefixWord ++ tailWord_1844680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844680).length < 2 ^ (prefixWord ++ tailWord_1844680).sum := by decide
  have hdescent : baseEnd_1844680 < baseStart_1844680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844684 : List Nat := [2, 2, 1, 4, 2, 2, 1, 4, 1, 4]
def baseStart_1844684 : Nat := 118140960795 + 1844684 * 2 ^ 59
def prefixEnd_1844684 : Nat := 4983230072969 + 3 ^ 40 * 1844684 * 2
def baseEnd_1844684 : Nat := 315736515886188633022153

theorem tailTrace_1844684 : CollatzResearch.WordTrace tailWord_1844684 prefixEnd_1844684 315736515886188633022153 := by
  unfold tailWord_1844684
  simp only [CollatzResearch.WordTrace]
  refine ⟨33640576424516194895070553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44854101899354926526760737 33640576424516194895070553)
  ·
    refine ⟨25230432318387146171302915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33640576424516194895070553 25230432318387146171302915)
    ·
      refine ⟨37845648477580719256954373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25230432318387146171302915 37845648477580719256954373)
      ·
        refine ⟨7096059089546384860678945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37845648477580719256954373 7096059089546384860678945)
        ·
          refine ⟨5322044317159788645509209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7096059089546384860678945 5322044317159788645509209)
          ·
            refine ⟨3991533237869841484131907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5322044317159788645509209 3991533237869841484131907)
            ·
              refine ⟨5987299856804762226197861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3991533237869841484131907 5987299856804762226197861)
              ·
                refine ⟨1122618723150892917412099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5987299856804762226197861 1122618723150892917412099)
                ·
                  refine ⟨1683928084726339376118149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1122618723150892917412099 1683928084726339376118149)
                  ·
                    refine ⟨315736515886188633022153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1683928084726339376118149 315736515886188633022153)
                    ·
                      rfl

theorem cell23_1844684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 4, 1, 4].length) (baseStart_1844684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1844684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1844684 prefixEnd_1844684 := by exact prefixLift 1844684
  have htrace : WordTrace (prefixWord ++ tailWord_1844684) baseStart_1844684 baseEnd_1844684 := by
    simpa [prefixWord, tailWord_1844684, baseEnd_1844684] using wordTrace_append hprefix tailTrace_1844684
  have hstable : (prefixWord ++ tailWord_1844684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844684).length < 2 ^ (prefixWord ++ tailWord_1844684).sum := by decide
  have hdescent : baseEnd_1844684 < baseStart_1844684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844703 : List Nat := [1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 7]
def baseStart_1844703 : Nat := 118140960795 + 1844703 * 2 ^ 59
def prefixEnd_1844703 : Nat := 4983230072969 + 3 ^ 40 * 1844703 * 2
def baseEnd_1844703 : Nat := 947219303791001324728871

theorem tailTrace_1844703 : CollatzResearch.WordTrace tailWord_1844703 prefixEnd_1844703 947219303791001324728871 := by
  unfold tailWord_1844703
  simp only [CollatzResearch.WordTrace]
  refine ⟨67281845835963556035082763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44854563890642370690055175 67281845835963556035082763)
  ·
    refine ⟨100922768753945334052624145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67281845835963556035082763 100922768753945334052624145)
    ·
      refine ⟨75692076565459000539468109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100922768753945334052624145 75692076565459000539468109)
      ·
        refine ⟨28384528712047125202300541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75692076565459000539468109 28384528712047125202300541)
        ·
          refine ⟨10644198267017671950862703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28384528712047125202300541 10644198267017671950862703)
          ·
            refine ⟨15966297400526507926294055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10644198267017671950862703 15966297400526507926294055)
            ·
              refine ⟨23949446100789761889441083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15966297400526507926294055 23949446100789761889441083)
              ·
                refine ⟨35924169151184642834161625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23949446100789761889441083 35924169151184642834161625)
                ·
                  refine ⟨26943126863388482125621219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35924169151184642834161625 26943126863388482125621219)
                  ·
                    refine ⟨40414690295082723188431829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26943126863388482125621219 40414690295082723188431829)
                    ·
                      refine ⟨947219303791001324728871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 40414690295082723188431829 947219303791001324728871)
                      ·
                        rfl

theorem cell23_1844703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_1844703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1844703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1844703 prefixEnd_1844703 := by exact prefixLift 1844703
  have htrace : WordTrace (prefixWord ++ tailWord_1844703) baseStart_1844703 baseEnd_1844703 := by
    simpa [prefixWord, tailWord_1844703, baseEnd_1844703] using wordTrace_append hprefix tailTrace_1844703
  have hstable : (prefixWord ++ tailWord_1844703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844703).length < 2 ^ (prefixWord ++ tailWord_1844703).sum := by decide
  have hdescent : baseEnd_1844703 < baseStart_1844703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844707 : List Nat := [1, 1, 1, 6, 2, 1, 1, 1, 5, 1, 3]
def baseStart_1844707 : Nat := 118140960795 + 1844707 * 2 ^ 59
def prefixEnd_1844707 : Nat := 4983230072969 + 3 ^ 40 * 1844707 * 2
def baseEnd_1844707 : Nat := 947221357713619309078853

theorem tailTrace_1844707 : CollatzResearch.WordTrace tailWord_1844707 prefixEnd_1844707 947221357713619309078853 := by
  unfold tailWord_1844707
  simp only [CollatzResearch.WordTrace]
  refine ⟨67281991727949064718228375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44854661151966043145485583 67281991727949064718228375)
  ·
    refine ⟨100922987591923597077342563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67281991727949064718228375 100922987591923597077342563)
    ·
      refine ⟨151384481387885395616013845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100922987591923597077342563 151384481387885395616013845)
      ·
        refine ⟨7096147565057127919500649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 151384481387885395616013845 7096147565057127919500649)
        ·
          refine ⟨5322110673792845939625487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7096147565057127919500649 5322110673792845939625487)
          ·
            refine ⟨7983166010689268909438231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5322110673792845939625487 7983166010689268909438231)
            ·
              refine ⟨11974749016033903364157347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7983166010689268909438231 11974749016033903364157347)
              ·
                refine ⟨17962123524050855046236021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11974749016033903364157347 17962123524050855046236021)
                ·
                  refine ⟨1683949080379767660584627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17962123524050855046236021 1683949080379767660584627)
                  ·
                    refine ⟨2525923620569651490876941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1683949080379767660584627 2525923620569651490876941)
                    ·
                      refine ⟨947221357713619309078853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2525923620569651490876941 947221357713619309078853)
                      ·
                        rfl

theorem cell23_1844707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_1844707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1844707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1844707 prefixEnd_1844707 := by exact prefixLift 1844707
  have htrace : WordTrace (prefixWord ++ tailWord_1844707) baseStart_1844707 baseEnd_1844707 := by
    simpa [prefixWord, tailWord_1844707, baseEnd_1844707] using wordTrace_append hprefix tailTrace_1844707
  have hstable : (prefixWord ++ tailWord_1844707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844707).length < 2 ^ (prefixWord ++ tailWord_1844707).sum := by decide
  have hdescent : baseEnd_1844707 < baseStart_1844707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844723 : List Nat := [1, 1, 1, 2, 2, 2, 2, 3, 3, 6]
def baseStart_1844723 : Nat := 118140960795 + 1844723 * 2 ^ 59
def prefixEnd_1844723 : Nat := 4983230072969 + 3 ^ 40 * 1844723 * 2
def baseEnd_1844723 : Nat := 315743191134697082159593

theorem tailTrace_1844723 : CollatzResearch.WordTrace tailWord_1844723 prefixEnd_1844723 315743191134697082159593 := by
  unfold tailWord_1844723
  simp only [CollatzResearch.WordTrace]
  refine ⟨67282575295891099450810823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44855050197260732967207215 67282575295891099450810823)
  ·
    refine ⟨100923862943836649176216235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67282575295891099450810823 100923862943836649176216235)
    ·
      refine ⟨151385794415754973764324353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100923862943836649176216235 151385794415754973764324353)
      ·
        refine ⟨113539345811816230323243265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151385794415754973764324353 113539345811816230323243265)
        ·
          refine ⟨85154509358862172742432449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113539345811816230323243265 85154509358862172742432449)
          ·
            refine ⟨63865882019146629556824337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85154509358862172742432449 63865882019146629556824337)
            ·
              refine ⟨47899411514359972167618253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63865882019146629556824337 47899411514359972167618253)
              ·
                refine ⟨17962279317884989562856845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47899411514359972167618253 17962279317884989562856845)
                ·
                  refine ⟨6735854744206871086071317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17962279317884989562856845 6735854744206871086071317)
                  ·
                    refine ⟨315743191134697082159593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6735854744206871086071317 315743191134697082159593)
                    ·
                      rfl

theorem cell23_1844723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 6].length) (baseStart_1844723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1844723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1844723 prefixEnd_1844723 := by exact prefixLift 1844723
  have htrace : WordTrace (prefixWord ++ tailWord_1844723) baseStart_1844723 baseEnd_1844723 := by
    simpa [prefixWord, tailWord_1844723, baseEnd_1844723] using wordTrace_append hprefix tailTrace_1844723
  have hstable : (prefixWord ++ tailWord_1844723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844723).length < 2 ^ (prefixWord ++ tailWord_1844723).sum := by decide
  have hdescent : baseEnd_1844723 < baseStart_1844723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844753 : List Nat := [1, 2, 2, 1, 1, 2, 4, 10]
def baseStart_1844753 : Nat := 118140960795 + 1844753 * 2 ^ 59
def prefixEnd_1844753 : Nat := 4983230072969 + 3 ^ 40 * 1844753 * 2
def baseEnd_1844753 : Nat := 35083147326804671448283

theorem tailTrace_1844753 : CollatzResearch.WordTrace tailWord_1844753 prefixEnd_1844753 35083147326804671448283 := by
  unfold tailWord_1844753
  simp only [CollatzResearch.WordTrace]
  refine ⟨67283669485782414574402913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44855779657188276382935275 67283669485782414574402913)
  ·
    refine ⟨50462752114336810930802185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67283669485782414574402913 50462752114336810930802185)
    ·
      refine ⟨37847064085752608198101639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50462752114336810930802185 37847064085752608198101639)
      ·
        refine ⟨56770596128628912297152459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37847064085752608198101639 56770596128628912297152459)
        ·
          refine ⟨85155894192943368445728689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56770596128628912297152459 85155894192943368445728689)
          ·
            refine ⟨63866920644707526334296517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85155894192943368445728689 63866920644707526334296517)
            ·
              refine ⟨11975047620882661187680597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63866920644707526334296517 11975047620882661187680597)
              ·
                refine ⟨35083147326804671448283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 11975047620882661187680597 35083147326804671448283)
                ·
                  rfl

theorem cell23_1844753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 10].length) (baseStart_1844753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1844753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1844753 prefixEnd_1844753 := by exact prefixLift 1844753
  have htrace : WordTrace (prefixWord ++ tailWord_1844753) baseStart_1844753 baseEnd_1844753 := by
    simpa [prefixWord, tailWord_1844753, baseEnd_1844753] using wordTrace_append hprefix tailTrace_1844753
  have hstable : (prefixWord ++ tailWord_1844753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844753).length < 2 ^ (prefixWord ++ tailWord_1844753).sum := by decide
  have hdescent : baseEnd_1844753 < baseStart_1844753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844757 : List Nat := [1, 3, 2, 1, 3, 4, 1, 1, 1, 6]
def baseStart_1844757 : Nat := 118140960795 + 1844757 * 2 ^ 59
def prefixEnd_1844757 : Nat := 4983230072969 + 3 ^ 40 * 1844757 * 2
def baseEnd_1844757 : Nat := 315749010582114704484541

theorem tailTrace_1844757 : CollatzResearch.WordTrace tailWord_1844757 prefixEnd_1844757 315749010582114704484541 := by
  unfold tailWord_1844757
  simp only [CollatzResearch.WordTrace]
  refine ⟨67283815377767923257548525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44855876918511948838365683 67283815377767923257548525)
  ·
    refine ⟨25231430766662971221580697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67283815377767923257548525 25231430766662971221580697)
    ·
      refine ⟨18923573074997228416185523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25231430766662971221580697 18923573074997228416185523)
      ·
        refine ⟨28385359612495842624278285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18923573074997228416185523 28385359612495842624278285)
        ·
          refine ⟨10644509854685940984104357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28385359612495842624278285 10644509854685940984104357)
          ·
            refine ⟨1995845597753613934519567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10644509854685940984104357 1995845597753613934519567)
            ·
              refine ⟨2993768396630420901779351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1995845597753613934519567 2993768396630420901779351)
              ·
                refine ⟨4490652594945631352669027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2993768396630420901779351 4490652594945631352669027)
                ·
                  refine ⟨6735978892418447029003541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4490652594945631352669027 6735978892418447029003541)
                  ·
                    refine ⟨315749010582114704484541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6735978892418447029003541 315749010582114704484541)
                    ·
                      rfl

theorem cell23_1844757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 1, 1, 6].length) (baseStart_1844757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1844757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1844757 prefixEnd_1844757 := by exact prefixLift 1844757
  have htrace : WordTrace (prefixWord ++ tailWord_1844757) baseStart_1844757 baseEnd_1844757 := by
    simpa [prefixWord, tailWord_1844757, baseEnd_1844757] using wordTrace_append hprefix tailTrace_1844757
  have hstable : (prefixWord ++ tailWord_1844757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844757).length < 2 ^ (prefixWord ++ tailWord_1844757).sum := by decide
  have hdescent : baseEnd_1844757 < baseStart_1844757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844764 : List Nat := [2, 2, 3, 1, 2, 1, 1, 4, 3, 2, 2]
def baseStart_1844764 : Nat := 118140960795 + 1844764 * 2 ^ 59
def prefixEnd_1844764 : Nat := 4983230072969 + 3 ^ 40 * 1844764 * 2
def baseEnd_1844764 : Nat := 947250626110925586066091

theorem tailTrace_1844764 : CollatzResearch.WordTrace tailWord_1844764 prefixEnd_1844764 947250626110925586066091 := by
  unfold tailWord_1844764
  simp only [CollatzResearch.WordTrace]
  refine ⟨33642035344371281726526673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44856047125828375635368897 33642035344371281726526673)
  ·
    refine ⟨25231526508278461294895005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33642035344371281726526673 25231526508278461294895005)
    ·
      refine ⟨9461822440604422985585627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25231526508278461294895005 9461822440604422985585627)
      ·
        refine ⟨14192733660906634478378441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9461822440604422985585627 14192733660906634478378441)
        ·
          refine ⟨10644550245679975858783831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14192733660906634478378441 10644550245679975858783831)
          ·
            refine ⟨15966825368519963788175747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10644550245679975858783831 15966825368519963788175747)
            ·
              refine ⟨23950238052779945682263621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15966825368519963788175747 23950238052779945682263621)
              ·
                refine ⟨4490669634896239815424429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23950238052779945682263621 4490669634896239815424429)
                ·
                  refine ⟨1684001113086089930784161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4490669634896239815424429 1684001113086089930784161)
                  ·
                    refine ⟨1263000834814567448088121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1684001113086089930784161 1263000834814567448088121)
                    ·
                      refine ⟨947250626110925586066091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1263000834814567448088121 947250626110925586066091)
                      ·
                        rfl

theorem cell23_1844764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4, 3, 2, 2].length) (baseStart_1844764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1844764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1844764 prefixEnd_1844764 := by exact prefixLift 1844764
  have htrace : WordTrace (prefixWord ++ tailWord_1844764) baseStart_1844764 baseEnd_1844764 := by
    simpa [prefixWord, tailWord_1844764, baseEnd_1844764] using wordTrace_append hprefix tailTrace_1844764
  have hstable : (prefixWord ++ tailWord_1844764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844764).length < 2 ^ (prefixWord ++ tailWord_1844764).sum := by decide
  have hdescent : baseEnd_1844764 < baseStart_1844764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844767 : List Nat := [1, 1, 2, 4, 1, 1, 3, 4, 1, 2, 3]
def baseStart_1844767 : Nat := 118140960795 + 1844767 * 2 ^ 59
def prefixEnd_1844767 : Nat := 4983230072969 + 3 ^ 40 * 1844767 * 2
def baseEnd_1844767 : Nat := 947252166552889074328577

theorem tailTrace_1844767 : CollatzResearch.WordTrace tailWord_1844767 prefixEnd_1844767 947252166552889074328577 := by
  unfold tailWord_1844767
  simp only [CollatzResearch.WordTrace]
  refine ⟨67284180107731694965412555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44856120071821129976941703 67284180107731694965412555)
  ·
    refine ⟨100926270161597542448118833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67284180107731694965412555 100926270161597542448118833)
    ·
      refine ⟨75694702621198156836089125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100926270161597542448118833 75694702621198156836089125)
      ·
        refine ⟨14192756741474654406766711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75694702621198156836089125 14192756741474654406766711)
        ·
          refine ⟨21289135112211981610150067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14192756741474654406766711 21289135112211981610150067)
          ·
            refine ⟨31933702668317972415225101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21289135112211981610150067 31933702668317972415225101)
            ·
              refine ⟨11975138500619239655709413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31933702668317972415225101 11975138500619239655709413)
              ·
                refine ⟨2245338468866107435445515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11975138500619239655709413 2245338468866107435445515)
                ·
                  refine ⟨3368007703299161153168273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2245338468866107435445515 3368007703299161153168273)
                  ·
                    refine ⟨2526005777474370864876205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3368007703299161153168273 2526005777474370864876205)
                    ·
                      refine ⟨947252166552889074328577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2526005777474370864876205 947252166552889074328577)
                      ·
                        rfl

theorem cell23_1844767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_1844767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1844767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1844767 prefixEnd_1844767 := by exact prefixLift 1844767
  have htrace : WordTrace (prefixWord ++ tailWord_1844767) baseStart_1844767 baseEnd_1844767 := by
    simpa [prefixWord, tailWord_1844767, baseEnd_1844767] using wordTrace_append hprefix tailTrace_1844767
  have hstable : (prefixWord ++ tailWord_1844767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844767).length < 2 ^ (prefixWord ++ tailWord_1844767).sum := by decide
  have hdescent : baseEnd_1844767 < baseStart_1844767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844860 : List Nat := [2, 2, 2, 1, 1, 2, 1, 5, 7]
def baseStart_1844860 : Nat := 118140960795 + 1844860 * 2 ^ 59
def prefixEnd_1844860 : Nat := 4983230072969 + 3 ^ 40 * 1844860 * 2
def baseEnd_1844860 : Nat := 105255546694861912273961

theorem tailTrace_1844860 : CollatzResearch.WordTrace tailWord_1844860 prefixEnd_1844860 105255546694861912273961 := by
  unfold tailWord_1844860
  simp only [CollatzResearch.WordTrace]
  refine ⟨33643786048197385924274017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44858381397596514565698689 33643786048197385924274017)
  ·
    refine ⟨25232839536148039443205513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33643786048197385924274017 25232839536148039443205513)
    ·
      refine ⟨18924629652111029582404135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25232839536148039443205513 18924629652111029582404135)
      ·
        refine ⟨28386944478166544373606203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18924629652111029582404135 28386944478166544373606203)
        ·
          refine ⟨42580416717249816560409305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28386944478166544373606203 42580416717249816560409305)
          ·
            refine ⟨31935312537937362420306979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42580416717249816560409305 31935312537937362420306979)
            ·
              refine ⟨47902968806906043630460469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31935312537937362420306979 47902968806906043630460469)
              ·
                refine ⟨4490903325647441590355669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47902968806906043630460469 4490903325647441590355669)
                ·
                  refine ⟨105255546694861912273961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4490903325647441590355669 105255546694861912273961)
                  ·
                    rfl

theorem cell23_1844860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5, 7].length) (baseStart_1844860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1844860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1844860 prefixEnd_1844860 := by exact prefixLift 1844860
  have htrace : WordTrace (prefixWord ++ tailWord_1844860) baseStart_1844860 baseEnd_1844860 := by
    simpa [prefixWord, tailWord_1844860, baseEnd_1844860] using wordTrace_append hprefix tailTrace_1844860
  have hstable : (prefixWord ++ tailWord_1844860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844860).length < 2 ^ (prefixWord ++ tailWord_1844860).sum := by decide
  have hdescent : baseEnd_1844860 < baseStart_1844860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844871 : List Nat := [1, 1, 4, 2, 1, 3, 2, 3, 2, 2, 2]
def baseStart_1844871 : Nat := 118140960795 + 1844871 * 2 ^ 59
def prefixEnd_1844871 : Nat := 4983230072969 + 3 ^ 40 * 1844871 * 2
def baseEnd_1844871 : Nat := 947305568540956667428099

theorem tailTrace_1844871 : CollatzResearch.WordTrace tailWord_1844871 prefixEnd_1844871 947305568540956667428099 := by
  unfold tailWord_1844871
  simp only [CollatzResearch.WordTrace]
  refine ⟨67287973299354920727198467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44858648866236613818132311 67287973299354920727198467)
  ·
    refine ⟨100931959949032381090797701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67287973299354920727198467 100931959949032381090797701)
    ·
      refine ⟨18924742490443571454524569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100931959949032381090797701 18924742490443571454524569)
      ·
        refine ⟨14193556867832678590893427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18924742490443571454524569 14193556867832678590893427)
        ·
          refine ⟨21290335301749017886340141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14193556867832678590893427 21290335301749017886340141)
          ·
            refine ⟨7983875738155881707377553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21290335301749017886340141 7983875738155881707377553)
            ·
              refine ⟨5987906803616911280533165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7983875738155881707377553 5987906803616911280533165)
              ·
                refine ⟨2245465051356341730199937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5987906803616911280533165 2245465051356341730199937)
                ·
                  refine ⟨1684098788517256297649953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2245465051356341730199937 1684098788517256297649953)
                  ·
                    refine ⟨1263074091387942223237465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1684098788517256297649953 1263074091387942223237465)
                    ·
                      refine ⟨947305568540956667428099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1263074091387942223237465 947305568540956667428099)
                      ·
                        rfl

theorem cell23_1844871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 3, 2, 2, 2].length) (baseStart_1844871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1844871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1844871 prefixEnd_1844871 := by exact prefixLift 1844871
  have htrace : WordTrace (prefixWord ++ tailWord_1844871) baseStart_1844871 baseEnd_1844871 := by
    simpa [prefixWord, tailWord_1844871, baseEnd_1844871] using wordTrace_append hprefix tailTrace_1844871
  have hstable : (prefixWord ++ tailWord_1844871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844871).length < 2 ^ (prefixWord ++ tailWord_1844871).sum := by decide
  have hdescent : baseEnd_1844871 < baseStart_1844871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844964 : List Nat := [2, 3, 1, 1, 1, 3, 3, 2, 2, 2, 3]
def baseStart_1844964 : Nat := 118140960795 + 1844964 * 2 ^ 59
def prefixEnd_1844964 : Nat := 4983230072969 + 3 ^ 40 * 1844964 * 2
def baseEnd_1844964 : Nat := 947353322241824803565171

theorem tailTrace_1844964 : CollatzResearch.WordTrace tailWord_1844964 prefixEnd_1844964 947353322241824803565171 := by
  unfold tailWord_1844964
  simp only [CollatzResearch.WordTrace]
  refine ⟨33645682644008998805166973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44860910192011998406889297 33645682644008998805166973)
  ·
    refine ⟨12617130991503374551937615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33645682644008998805166973 12617130991503374551937615)
    ·
      refine ⟨18925696487255061827906423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12617130991503374551937615 18925696487255061827906423)
      ·
        refine ⟨28388544730882592741859635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18925696487255061827906423 28388544730882592741859635)
        ·
          refine ⟨42582817096323889112789453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28388544730882592741859635 42582817096323889112789453)
          ·
            refine ⟨15968556411121458417296045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42582817096323889112789453 15968556411121458417296045)
            ·
              refine ⟨5988208654170546906486017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15968556411121458417296045 5988208654170546906486017)
              ·
                refine ⟨4491156490627910179864513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5988208654170546906486017 4491156490627910179864513)
                ·
                  refine ⟨3368367367970932634898385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4491156490627910179864513 3368367367970932634898385)
                  ·
                    refine ⟨2526275525978199476173789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3368367367970932634898385 2526275525978199476173789)
                    ·
                      refine ⟨947353322241824803565171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2526275525978199476173789 947353322241824803565171)
                      ·
                        rfl

theorem cell23_1844964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2, 2, 2, 3].length) (baseStart_1844964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1844964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1844964 prefixEnd_1844964 := by exact prefixLift 1844964
  have htrace : WordTrace (prefixWord ++ tailWord_1844964) baseStart_1844964 baseEnd_1844964 := by
    simpa [prefixWord, tailWord_1844964, baseEnd_1844964] using wordTrace_append hprefix tailTrace_1844964
  have hstable : (prefixWord ++ tailWord_1844964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844964).length < 2 ^ (prefixWord ++ tailWord_1844964).sum := by decide
  have hdescent : baseEnd_1844964 < baseStart_1844964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845004 : List Nat := [2, 2, 1, 2, 2, 1, 2, 3, 1, 5, 2]
def baseStart_1845004 : Nat := 118140960795 + 1845004 * 2 ^ 59
def prefixEnd_1845004 : Nat := 4983230072969 + 3 ^ 40 * 1845004 * 2
def baseEnd_1845004 : Nat := 947373861468004647064987

theorem tailTrace_1845004 : CollatzResearch.WordTrace tailWord_1845004 prefixEnd_1845004 947373861468004647064987 := by
  unfold tailWord_1845004
  simp only [CollatzResearch.WordTrace]
  refine ⟨33646412103936542220895033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44861882805248722961193377 33646412103936542220895033)
  ·
    refine ⟨25234809077952406665671275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33646412103936542220895033 25234809077952406665671275)
    ·
      refine ⟨37852213616928609998506913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25234809077952406665671275 37852213616928609998506913)
      ·
        refine ⟨28389160212696457498880185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37852213616928609998506913 28389160212696457498880185)
        ·
          refine ⟨21291870159522343124160139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28389160212696457498880185 21291870159522343124160139)
          ·
            refine ⟨31937805239283514686240209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21291870159522343124160139 31937805239283514686240209)
            ·
              refine ⟨23953353929462636014680157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31937805239283514686240209 23953353929462636014680157)
              ·
                refine ⟨8982507723548488505505059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23953353929462636014680157 8982507723548488505505059)
                ·
                  refine ⟨13473761585322732758257589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8982507723548488505505059 13473761585322732758257589)
                  ·
                    refine ⟨1263165148624006196086649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13473761585322732758257589 1263165148624006196086649)
                    ·
                      refine ⟨947373861468004647064987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1263165148624006196086649 947373861468004647064987)
                      ·
                        rfl

theorem cell23_1845004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 1, 5, 2].length) (baseStart_1845004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1845004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1845004 prefixEnd_1845004 := by exact prefixLift 1845004
  have htrace : WordTrace (prefixWord ++ tailWord_1845004) baseStart_1845004 baseEnd_1845004 := by
    simpa [prefixWord, tailWord_1845004, baseEnd_1845004] using wordTrace_append hprefix tailTrace_1845004
  have hstable : (prefixWord ++ tailWord_1845004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845004).length < 2 ^ (prefixWord ++ tailWord_1845004).sum := by decide
  have hdescent : baseEnd_1845004 < baseStart_1845004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845022 : List Nat := [4, 3, 2, 2, 1, 1, 1, 4, 1, 4]
def baseStart_1845022 : Nat := 118140960795 + 1845022 * 2 ^ 59
def prefixEnd_1845022 : Nat := 4983230072969 + 3 ^ 40 * 1845022 * 2
def baseEnd_1845022 : Nat := 315794368039928525546635

theorem tailTrace_1845022 : CollatzResearch.WordTrace tailWord_1845022 prefixEnd_1845022 315794368039928525546635 := by
  unfold tailWord_1845022
  simp only [CollatzResearch.WordTrace]
  refine ⟨8411685090225984189493165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44862320481205249010630213 8411685090225984189493165)
  ·
    refine ⟨3154381908834744071059937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8411685090225984189493165 3154381908834744071059937)
    ·
      refine ⟨2365786431626058053294953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3154381908834744071059937 2365786431626058053294953)
      ·
        refine ⟨1774339823719543539971215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2365786431626058053294953 1774339823719543539971215)
        ·
          refine ⟨2661509735579315309956823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1774339823719543539971215 2661509735579315309956823)
          ·
            refine ⟨3992264603368972964935235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2661509735579315309956823 3992264603368972964935235)
            ·
              refine ⟨5988396905053459447402853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3992264603368972964935235 5988396905053459447402853)
              ·
                refine ⟨1122824419697523646388035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5988396905053459447402853 1122824419697523646388035)
                ·
                  refine ⟨1684236629546285469582053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1122824419697523646388035 1684236629546285469582053)
                  ·
                    refine ⟨315794368039928525546635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1684236629546285469582053 315794368039928525546635)
                    ·
                      rfl

theorem cell23_1845022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_1845022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1845022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1845022 prefixEnd_1845022 := by exact prefixLift 1845022
  have htrace : WordTrace (prefixWord ++ tailWord_1845022) baseStart_1845022 baseEnd_1845022 := by
    simpa [prefixWord, tailWord_1845022, baseEnd_1845022] using wordTrace_append hprefix tailTrace_1845022
  have hstable : (prefixWord ++ tailWord_1845022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845022).length < 2 ^ (prefixWord ++ tailWord_1845022).sum := by decide
  have hdescent : baseEnd_1845022 < baseStart_1845022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845055 : List Nat := [1, 1, 2, 2, 7, 1, 1, 1, 2, 3, 2]
def baseStart_1845055 : Nat := 118140960795 + 1845055 * 2 ^ 59
def prefixEnd_1845055 : Nat := 4983230072969 + 3 ^ 40 * 1845055 * 2
def baseEnd_1845055 : Nat := 947400048981383947527253

theorem tailTrace_1845055 : CollatzResearch.WordTrace tailWord_1845055 prefixEnd_1845055 947400048981383947527253 := by
  unfold tailWord_1845055
  simp only [CollatzResearch.WordTrace]
  refine ⟨67294684330688320151896619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44863122887125546767931079 67294684330688320151896619)
  ·
    refine ⟨100942026496032480227844929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67294684330688320151896619 100942026496032480227844929)
    ·
      refine ⟨75706519872024360170883697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100942026496032480227844929 75706519872024360170883697)
      ·
        refine ⟨56779889904018270128162773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75706519872024360170883697 56779889904018270128162773)
        ·
          refine ⟨1330778669625428206128815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 56779889904018270128162773 1330778669625428206128815)
          ·
            refine ⟨1996168004438142309193223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1330778669625428206128815 1996168004438142309193223)
            ·
              refine ⟨2994252006657213463789835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1996168004438142309193223 2994252006657213463789835)
              ·
                refine ⟨4491378009985820195684753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2994252006657213463789835 4491378009985820195684753)
                ·
                  refine ⟨3368533507489365146763565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4491378009985820195684753 3368533507489365146763565)
                  ·
                    refine ⟨1263200065308511930036337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3368533507489365146763565 1263200065308511930036337)
                    ·
                      refine ⟨947400048981383947527253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1263200065308511930036337 947400048981383947527253)
                      ·
                        rfl

theorem cell23_1845055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 1, 2, 3, 2].length) (baseStart_1845055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1845055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1845055 prefixEnd_1845055 := by exact prefixLift 1845055
  have htrace : WordTrace (prefixWord ++ tailWord_1845055) baseStart_1845055 baseEnd_1845055 := by
    simpa [prefixWord, tailWord_1845055, baseEnd_1845055] using wordTrace_append hprefix tailTrace_1845055
  have hstable : (prefixWord ++ tailWord_1845055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845055).length < 2 ^ (prefixWord ++ tailWord_1845055).sum := by decide
  have hdescent : baseEnd_1845055 < baseStart_1845055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845062 : List Nat := [6, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3]
def baseStart_1845062 : Nat := 118140960795 + 1845062 * 2 ^ 59
def prefixEnd_1845062 : Nat := 4983230072969 + 3 ^ 40 * 1845062 * 2
def baseEnd_1845062 : Nat := 947403643345965420139721

theorem tailTrace_1845062 : CollatzResearch.WordTrace tailWord_1845062 prefixEnd_1845062 947403643345965420139721 := by
  unfold tailWord_1845062
  simp only [CollatzResearch.WordTrace]
  refine ⟨2102966863801967510856295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 44863293094441973564934293 2102966863801967510856295)
  ·
    refine ⟨3154450295702951266284443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2102966863801967510856295 3154450295702951266284443)
    ·
      refine ⟨4731675443554426899426665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3154450295702951266284443 4731675443554426899426665)
      ·
        refine ⟨3548756582665820174569999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4731675443554426899426665 3548756582665820174569999)
        ·
          refine ⟨5323134873998730261854999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3548756582665820174569999 5323134873998730261854999)
          ·
            refine ⟨7984702310998095392782499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5323134873998730261854999 7984702310998095392782499)
            ·
              refine ⟨11977053466497143089173749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7984702310998095392782499 11977053466497143089173749)
              ·
                refine ⟨1122848762484107164610039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11977053466497143089173749 1122848762484107164610039)
                ·
                  refine ⟨1684273143726160746915059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1122848762484107164610039 1684273143726160746915059)
                  ·
                    refine ⟨2526409715589241120372589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1684273143726160746915059 2526409715589241120372589)
                    ·
                      refine ⟨947403643345965420139721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2526409715589241120372589 947403643345965420139721)
                      ·
                        rfl

theorem cell23_1845062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_1845062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1845062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1845062 prefixEnd_1845062 := by exact prefixLift 1845062
  have htrace : WordTrace (prefixWord ++ tailWord_1845062) baseStart_1845062 baseEnd_1845062 := by
    simpa [prefixWord, tailWord_1845062, baseEnd_1845062] using wordTrace_append hprefix tailTrace_1845062
  have hstable : (prefixWord ++ tailWord_1845062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845062).length < 2 ^ (prefixWord ++ tailWord_1845062).sum := by decide
  have hdescent : baseEnd_1845062 < baseStart_1845062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845064 : List Nat := [2, 1, 3, 1, 1, 4, 2, 2, 1, 2, 4]
def baseStart_1845064 : Nat := 118140960795 + 1845064 * 2 ^ 59
def prefixEnd_1845064 : Nat := 4983230072969 + 3 ^ 40 * 1845064 * 2
def baseEnd_1845064 : Nat := 947404670307274412314711

theorem tailTrace_1845064 : CollatzResearch.WordTrace tailWord_1845064 prefixEnd_1845064 947404670307274412314711 := by
  unfold tailWord_1845064
  simp only [CollatzResearch.WordTrace]
  refine ⟨33647506293827857344487123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44863341725103809792649497 33647506293827857344487123)
  ·
    refine ⟨50471259440741786016730685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33647506293827857344487123 50471259440741786016730685)
    ·
      refine ⟨18926722290278169756274007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50471259440741786016730685 18926722290278169756274007)
      ·
        refine ⟨28390083435417254634411011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18926722290278169756274007 28390083435417254634411011)
        ·
          refine ⟨42585125153125881951616517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28390083435417254634411011 42585125153125881951616517)
          ·
            refine ⟨7984710966211102865928097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42585125153125881951616517 7984710966211102865928097)
            ·
              refine ⟨5988533224658327149446073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7984710966211102865928097 5988533224658327149446073)
              ·
                refine ⟨4491399918493745362084555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5988533224658327149446073 4491399918493745362084555)
                ·
                  refine ⟨6737099877740618043126833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4491399918493745362084555 6737099877740618043126833)
                  ·
                    refine ⟨5052824908305463532345125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6737099877740618043126833 5052824908305463532345125)
                    ·
                      refine ⟨947404670307274412314711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5052824908305463532345125 947404670307274412314711)
                      ·
                        rfl

theorem cell23_1845064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2, 1, 2, 4].length) (baseStart_1845064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1845064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1845064 prefixEnd_1845064 := by exact prefixLift 1845064
  have htrace : WordTrace (prefixWord ++ tailWord_1845064) baseStart_1845064 baseEnd_1845064 := by
    simpa [prefixWord, tailWord_1845064, baseEnd_1845064] using wordTrace_append hprefix tailTrace_1845064
  have hstable : (prefixWord ++ tailWord_1845064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845064).length < 2 ^ (prefixWord ++ tailWord_1845064).sum := by decide
  have hdescent : baseEnd_1845064 < baseStart_1845064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845097 : List Nat := [1, 2, 1, 1, 1, 3, 1, 2, 4, 2, 5]
def baseStart_1845097 : Nat := 118140960795 + 1845097 * 2 ^ 59
def prefixEnd_1845097 : Nat := 4983230072969 + 3 ^ 40 * 1845097 * 2
def baseEnd_1845097 : Nat := 947421615168872783202059

theorem tailTrace_1845097 : CollatzResearch.WordTrace tailWord_1845097 prefixEnd_1845097 947421615168872783202059 := by
  unfold tailWord_1845097
  simp only [CollatzResearch.WordTrace]
  refine ⟨67296216196536161324925545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44864144131024107549950363 67296216196536161324925545)
  ·
    refine ⟨50472162147402120993694159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67296216196536161324925545 50472162147402120993694159)
    ·
      refine ⟨75708243221103181490541239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50472162147402120993694159 75708243221103181490541239)
      ·
        refine ⟨113562364831654772235811859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75708243221103181490541239 113562364831654772235811859)
        ·
          refine ⟨170343547247482158353717789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113562364831654772235811859 170343547247482158353717789)
          ·
            refine ⟨63878830217805809382644171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170343547247482158353717789 63878830217805809382644171)
            ·
              refine ⟨95818245326708714073966257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63878830217805809382644171 95818245326708714073966257)
              ·
                refine ⟨71863683995031535555474693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95818245326708714073966257 71863683995031535555474693)
                ·
                  refine ⟨13474440749068412916651505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71863683995031535555474693 13474440749068412916651505)
                  ·
                    refine ⟨10105830561801309687488629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13474440749068412916651505 10105830561801309687488629)
                    ·
                      refine ⟨947421615168872783202059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10105830561801309687488629 947421615168872783202059)
                      ·
                        rfl

theorem cell23_1845097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 2, 5].length) (baseStart_1845097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1845097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1845097 prefixEnd_1845097 := by exact prefixLift 1845097
  have htrace : WordTrace (prefixWord ++ tailWord_1845097) baseStart_1845097 baseEnd_1845097 := by
    simpa [prefixWord, tailWord_1845097, baseEnd_1845097] using wordTrace_append hprefix tailTrace_1845097
  have hstable : (prefixWord ++ tailWord_1845097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845097).length < 2 ^ (prefixWord ++ tailWord_1845097).sum := by decide
  have hdescent : baseEnd_1845097 < baseStart_1845097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845101 : List Nat := [1, 5, 1, 1, 1, 1, 5, 1, 1, 3, 3]
def baseStart_1845101 : Nat := 118140960795 + 1845101 * 2 ^ 59
def prefixEnd_1845101 : Nat := 4983230072969 + 3 ^ 40 * 1845101 * 2
def baseEnd_1845101 : Nat := 947423669091490767552041

theorem tailTrace_1845101 : CollatzResearch.WordTrace tailWord_1845101 prefixEnd_1845101 947423669091490767552041 := by
  unfold tailWord_1845101
  simp only [CollatzResearch.WordTrace]
  refine ⟨67296362088521670008071157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44864241392347780005380771 67296362088521670008071157)
  ·
    refine ⟨6309033945798906563256671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67296362088521670008071157 6309033945798906563256671)
    ·
      refine ⟨9463550918698359844885007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6309033945798906563256671 9463550918698359844885007)
      ·
        refine ⟨14195326378047539767327511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9463550918698359844885007 14195326378047539767327511)
        ·
          refine ⟨21292989567071309650991267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14195326378047539767327511 21292989567071309650991267)
          ·
            refine ⟨31939484350606964476486901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21292989567071309650991267 31939484350606964476486901)
            ·
              refine ⟨2994326657869402919670647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31939484350606964476486901 2994326657869402919670647)
              ·
                refine ⟨4491489986804104379505971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2994326657869402919670647 4491489986804104379505971)
                ·
                  refine ⟨6737234980206156569258957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4491489986804104379505971 6737234980206156569258957)
                  ·
                    refine ⟨2526463117577308713472109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6737234980206156569258957 2526463117577308713472109)
                    ·
                      refine ⟨947423669091490767552041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2526463117577308713472109 947423669091490767552041)
                      ·
                        rfl

theorem cell23_1845101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_1845101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1845101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1845101 prefixEnd_1845101 := by exact prefixLift 1845101
  have htrace : WordTrace (prefixWord ++ tailWord_1845101) baseStart_1845101 baseEnd_1845101 := by
    simpa [prefixWord, tailWord_1845101, baseEnd_1845101] using wordTrace_append hprefix tailTrace_1845101
  have hstable : (prefixWord ++ tailWord_1845101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845101).length < 2 ^ (prefixWord ++ tailWord_1845101).sum := by decide
  have hdescent : baseEnd_1845101 < baseStart_1845101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845231 : List Nat := [1, 1, 2, 1, 4, 2, 1, 2, 1, 6, 2]
def baseStart_1845231 : Nat := 118140960795 + 1845231 * 2 ^ 59
def prefixEnd_1845231 : Nat := 4983230072969 + 3 ^ 40 * 1845231 * 2
def baseEnd_1845231 : Nat := 947490421576575258926443

theorem tailTrace_1845231 : CollatzResearch.WordTrace tailWord_1845231 prefixEnd_1845231 947490421576575258926443 := by
  unfold tailWord_1845231
  simp only [CollatzResearch.WordTrace]
  refine ⟨67301103578050702210303547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44867402385367134806869031 67301103578050702210303547)
  ·
    refine ⟨100951655367076053315455321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67301103578050702210303547 100951655367076053315455321)
    ·
      refine ⟨75713741525307039986591491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100951655367076053315455321 75713741525307039986591491)
      ·
        refine ⟨113570612287960559979887237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75713741525307039986591491 113570612287960559979887237)
        ·
          refine ⟨21294489803992604996228857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113570612287960559979887237 21294489803992604996228857)
          ·
            refine ⟨15970867352994453747171643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21294489803992604996228857 15970867352994453747171643)
            ·
              refine ⟨23956301029491680620757465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15970867352994453747171643 23956301029491680620757465)
              ·
                refine ⟨17967225772118760465568099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23956301029491680620757465 17967225772118760465568099)
                ·
                  refine ⟨26950838658178140698352149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17967225772118760465568099 26950838658178140698352149)
                  ·
                    refine ⟨1263320562102100345235257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26950838658178140698352149 1263320562102100345235257)
                    ·
                      refine ⟨947490421576575258926443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1263320562102100345235257 947490421576575258926443)
                      ·
                        rfl

theorem cell23_1845231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 6, 2].length) (baseStart_1845231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1845231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1845231 prefixEnd_1845231 := by exact prefixLift 1845231
  have htrace : WordTrace (prefixWord ++ tailWord_1845231) baseStart_1845231 baseEnd_1845231 := by
    simpa [prefixWord, tailWord_1845231, baseEnd_1845231] using wordTrace_append hprefix tailTrace_1845231
  have hstable : (prefixWord ++ tailWord_1845231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845231).length < 2 ^ (prefixWord ++ tailWord_1845231).sum := by decide
  have hdescent : baseEnd_1845231 < baseStart_1845231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845244 : List Nat := [2, 2, 2, 1, 2, 2, 1, 1, 1, 3, 6]
def baseStart_1845244 : Nat := 118140960795 + 1845244 * 2 ^ 59
def prefixEnd_1845244 : Nat := 4983230072969 + 3 ^ 40 * 1845244 * 2
def baseEnd_1845244 : Nat := 947497096825083708063883

theorem tailTrace_1845244 : CollatzResearch.WordTrace tailWord_1845244 prefixEnd_1845244 947497096825083708063883 := by
  unfold tailWord_1845244
  simp only [CollatzResearch.WordTrace]
  refine ⟨33650788863501802715263393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44867718484669070287017857 33650788863501802715263393)
  ·
    refine ⟨25238091647626352036447545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33650788863501802715263393 25238091647626352036447545)
    ·
      refine ⟨18928568735719764027335659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25238091647626352036447545 18928568735719764027335659)
      ·
        refine ⟨28392853103579646041003489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18928568735719764027335659 28392853103579646041003489)
        ·
          refine ⟨21294639827684734530752617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28392853103579646041003489 21294639827684734530752617)
          ·
            refine ⟨15970979870763550898064463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21294639827684734530752617 15970979870763550898064463)
            ·
              refine ⟨23956469806145326347096695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15970979870763550898064463 23956469806145326347096695)
              ·
                refine ⟨35934704709217989520645043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23956469806145326347096695 35934704709217989520645043)
                ·
                  refine ⟨53902057063826984280967565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35934704709217989520645043 53902057063826984280967565)
                  ·
                    refine ⟨20213271398935119105362837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53902057063826984280967565 20213271398935119105362837)
                    ·
                      refine ⟨947497096825083708063883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20213271398935119105362837 947497096825083708063883)
                      ·
                        rfl

theorem cell23_1845244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_1845244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1845244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1845244 prefixEnd_1845244 := by exact prefixLift 1845244
  have htrace : WordTrace (prefixWord ++ tailWord_1845244) baseStart_1845244 baseEnd_1845244 := by
    simpa [prefixWord, tailWord_1845244, baseEnd_1845244] using wordTrace_append hprefix tailTrace_1845244
  have hstable : (prefixWord ++ tailWord_1845244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845244).length < 2 ^ (prefixWord ++ tailWord_1845244).sum := by decide
  have hdescent : baseEnd_1845244 < baseStart_1845244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845251 : List Nat := [1, 1, 1, 3, 2, 1, 1, 6, 2, 2, 3]
def baseStart_1845251 : Nat := 118140960795 + 1845251 * 2 ^ 59
def prefixEnd_1845251 : Nat := 4983230072969 + 3 ^ 40 * 1845251 * 2
def baseEnd_1845251 : Nat := 947500691189665180676351

theorem tailTrace_1845251 : CollatzResearch.WordTrace tailWord_1845251 prefixEnd_1845251 947500691189665180676351 := by
  unfold tailWord_1845251
  simp only [CollatzResearch.WordTrace]
  refine ⟨67301833037978245626031607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44867888691985497084021071 67301833037978245626031607)
  ·
    refine ⟨100952749556967368439047411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67301833037978245626031607 100952749556967368439047411)
    ·
      refine ⟨151429124335451052658571117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100952749556967368439047411 151429124335451052658571117)
      ·
        refine ⟨56785921625794144746964169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151429124335451052658571117 56785921625794144746964169)
        ·
          refine ⟨42589441219345608560223127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56785921625794144746964169 42589441219345608560223127)
          ·
            refine ⟨63884161829018412840334691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42589441219345608560223127 63884161829018412840334691)
            ·
              refine ⟨95826242743527619260502037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63884161829018412840334691 95826242743527619260502037)
              ·
                refine ⟨4491855128602857152836033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 95826242743527619260502037 4491855128602857152836033)
                ·
                  refine ⟨3368891346452142864627025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4491855128602857152836033 3368891346452142864627025)
                  ·
                    refine ⟨2526668509839107148470269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3368891346452142864627025 2526668509839107148470269)
                    ·
                      refine ⟨947500691189665180676351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2526668509839107148470269 947500691189665180676351)
                      ·
                        rfl

theorem cell23_1845251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6, 2, 2, 3].length) (baseStart_1845251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1845251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1845251 prefixEnd_1845251 := by exact prefixLift 1845251
  have htrace : WordTrace (prefixWord ++ tailWord_1845251) baseStart_1845251 baseEnd_1845251 := by
    simpa [prefixWord, tailWord_1845251, baseEnd_1845251] using wordTrace_append hprefix tailTrace_1845251
  have hstable : (prefixWord ++ tailWord_1845251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845251).length < 2 ^ (prefixWord ++ tailWord_1845251).sum := by decide
  have hdescent : baseEnd_1845251 < baseStart_1845251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845321 : List Nat := [1, 2, 1, 1, 2, 2, 4, 2, 3, 1, 4]
def baseStart_1845321 : Nat := 118140960795 + 1845321 * 2 ^ 59
def prefixEnd_1845321 : Nat := 4983230072969 + 3 ^ 40 * 1845321 * 2
def baseEnd_1845321 : Nat := 947536634835479906801029

theorem tailTrace_1845321 : CollatzResearch.WordTrace tailWord_1845321 prefixEnd_1845321 947536634835479906801029 := by
  unfold tailWord_1845321
  simp only [CollatzResearch.WordTrace]
  refine ⟨67304386147724647581079817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44869590765149765054053211 67304386147724647581079817)
  ·
    refine ⟨50478289610793485685809863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67304386147724647581079817 50478289610793485685809863)
    ·
      refine ⟨75717434416190228528714795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50478289610793485685809863 75717434416190228528714795)
      ·
        refine ⟨113576151624285342793072193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75717434416190228528714795 113576151624285342793072193)
        ·
          refine ⟨85182113718214007094804145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113576151624285342793072193 85182113718214007094804145)
          ·
            refine ⟨63886585288660505321103109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85182113718214007094804145 63886585288660505321103109)
            ·
              refine ⟨11978734741623844747706833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63886585288660505321103109 11978734741623844747706833)
              ·
                refine ⟨8984051056217883560780125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11978734741623844747706833 8984051056217883560780125)
                ·
                  refine ⟨3369019146081706335292547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8984051056217883560780125 3369019146081706335292547)
                  ·
                    refine ⟨5053528719122559502938821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3369019146081706335292547 5053528719122559502938821)
                    ·
                      refine ⟨947536634835479906801029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5053528719122559502938821 947536634835479906801029)
                      ·
                        rfl

theorem cell23_1845321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 3, 1, 4].length) (baseStart_1845321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1845321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1845321 prefixEnd_1845321 := by exact prefixLift 1845321
  have htrace : WordTrace (prefixWord ++ tailWord_1845321) baseStart_1845321 baseEnd_1845321 := by
    simpa [prefixWord, tailWord_1845321, baseEnd_1845321] using wordTrace_append hprefix tailTrace_1845321
  have hstable : (prefixWord ++ tailWord_1845321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845321).length < 2 ^ (prefixWord ++ tailWord_1845321).sum := by decide
  have hdescent : baseEnd_1845321 < baseStart_1845321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845325 : List Nat := [1, 6, 1, 1, 1, 1, 1, 2, 4, 3, 2]
def baseStart_1845325 : Nat := 118140960795 + 1845325 * 2 ^ 59
def prefixEnd_1845325 : Nat := 4983230072969 + 3 ^ 40 * 1845325 * 2
def baseEnd_1845325 : Nat := 947538688758097891151011

theorem tailTrace_1845325 : CollatzResearch.WordTrace tailWord_1845325 prefixEnd_1845325 947538688758097891151011 := by
  unfold tailWord_1845325
  simp only [CollatzResearch.WordTrace]
  refine ⟨67304532039710156264225429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44869688026473437509483619 67304532039710156264225429)
  ·
    refine ⟨3154899939361413574885567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 67304532039710156264225429 3154899939361413574885567)
    ·
      refine ⟨4732349909042120362328351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3154899939361413574885567 4732349909042120362328351)
      ·
        refine ⟨7098524863563180543492527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4732349909042120362328351 7098524863563180543492527)
        ·
          refine ⟨10647787295344770815238791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7098524863563180543492527 10647787295344770815238791)
          ·
            refine ⟨15971680943017156222858187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10647787295344770815238791 15971680943017156222858187)
            ·
              refine ⟨23957521414525734334287281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15971680943017156222858187 23957521414525734334287281)
              ·
                refine ⟨17968141060894300750715461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23957521414525734334287281 17968141060894300750715461)
                ·
                  refine ⟨3369026448917681390759149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17968141060894300750715461 3369026448917681390759149)
                  ·
                    refine ⟨1263384918344130521534681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3369026448917681390759149 1263384918344130521534681)
                    ·
                      refine ⟨947538688758097891151011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1263384918344130521534681 947538688758097891151011)
                      ·
                        rfl

theorem cell23_1845325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_1845325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1845325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1845325 prefixEnd_1845325 := by exact prefixLift 1845325
  have htrace : WordTrace (prefixWord ++ tailWord_1845325) baseStart_1845325 baseEnd_1845325 := by
    simpa [prefixWord, tailWord_1845325, baseEnd_1845325] using wordTrace_append hprefix tailTrace_1845325
  have hstable : (prefixWord ++ tailWord_1845325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845325).length < 2 ^ (prefixWord ++ tailWord_1845325).sum := by decide
  have hdescent : baseEnd_1845325 < baseStart_1845325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845366 : List Nat := [5, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3]
def baseStart_1845366 : Nat := 118140960795 + 1845366 * 2 ^ 59
def prefixEnd_1845366 : Nat := 4983230072969 + 3 ^ 40 * 1845366 * 2
def baseEnd_1845366 : Nat := 947559741464932230738323

theorem tailTrace_1845366 : CollatzResearch.WordTrace tailWord_1845366 prefixEnd_1845366 947559741464932230738323 := by
  unfold tailWord_1845366
  simp only [CollatzResearch.WordTrace]
  refine ⟨4206626714535101266654247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44870684955041080177645301 4206626714535101266654247)
  ·
    refine ⟨6309940071802651899981371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4206626714535101266654247 6309940071802651899981371)
    ·
      refine ⟨9464910107703977849972057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6309940071802651899981371 9464910107703977849972057)
      ·
        refine ⟨7098682580777983387479043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9464910107703977849972057 7098682580777983387479043)
        ·
          refine ⟨10648023871166975081218565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7098682580777983387479043 10648023871166975081218565)
          ·
            refine ⟨1996504475843807827728481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10648023871166975081218565 1996504475843807827728481)
            ·
              refine ⟨1497378356882855870796361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1996504475843807827728481 1497378356882855870796361)
              ·
                refine ⟨1123033767662141903097271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1497378356882855870796361 1123033767662141903097271)
                ·
                  refine ⟨1684550651493212854645907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1123033767662141903097271 1684550651493212854645907)
                  ·
                    refine ⟨2526825977239819281968861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1684550651493212854645907 2526825977239819281968861)
                    ·
                      refine ⟨947559741464932230738323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2526825977239819281968861 947559741464932230738323)
                      ·
                        rfl

theorem cell23_1845366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_1845366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1845366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1845366 prefixEnd_1845366 := by exact prefixLift 1845366
  have htrace : WordTrace (prefixWord ++ tailWord_1845366) baseStart_1845366 baseEnd_1845366 := by
    simpa [prefixWord, tailWord_1845366, baseEnd_1845366] using wordTrace_append hprefix tailTrace_1845366
  have hstable : (prefixWord ++ tailWord_1845366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845366).length < 2 ^ (prefixWord ++ tailWord_1845366).sum := by decide
  have hdescent : baseEnd_1845366 < baseStart_1845366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845388 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 8, 1, 3]
def baseStart_1845388 : Nat := 118140960795 + 1845388 * 2 ^ 59
def prefixEnd_1845388 : Nat := 4983230072969 + 3 ^ 40 * 1845388 * 2
def baseEnd_1845388 : Nat := 947571038039331144663221

theorem tailTrace_1845388 : CollatzResearch.WordTrace tailWord_1845388 prefixEnd_1845388 947571038039331144663221 := by
  unfold tailWord_1845388
  simp only [CollatzResearch.WordTrace]
  refine ⟨33653414919240959011884409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44871219892321278682512545 33653414919240959011884409)
  ·
    refine ⟨25240061189430719258913307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33653414919240959011884409 25240061189430719258913307)
    ·
      refine ⟨37860091784146078888369961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25240061189430719258913307 37860091784146078888369961)
      ·
        refine ⟨28395068838109559166277471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37860091784146078888369961 28395068838109559166277471)
        ·
          refine ⟨42592603257164338749416207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28395068838109559166277471 42592603257164338749416207)
          ·
            refine ⟨63888904885746508124124311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42592603257164338749416207 63888904885746508124124311)
            ·
              refine ⟨95833357328619762186186467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63888904885746508124124311 95833357328619762186186467)
              ·
                refine ⟨143750035992929643279279701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95833357328619762186186467 143750035992929643279279701)
                ·
                  refine ⟨1684570734292144257179059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 143750035992929643279279701 1684570734292144257179059)
                  ·
                    refine ⟨2526856101438216385768589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1684570734292144257179059 2526856101438216385768589)
                    ·
                      refine ⟨947571038039331144663221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2526856101438216385768589 947571038039331144663221)
                      ·
                        rfl

theorem cell23_1845388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 8, 1, 3].length) (baseStart_1845388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1845388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1845388 prefixEnd_1845388 := by exact prefixLift 1845388
  have htrace : WordTrace (prefixWord ++ tailWord_1845388) baseStart_1845388 baseEnd_1845388 := by
    simpa [prefixWord, tailWord_1845388, baseEnd_1845388] using wordTrace_append hprefix tailTrace_1845388
  have hstable : (prefixWord ++ tailWord_1845388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845388).length < 2 ^ (prefixWord ++ tailWord_1845388).sum := by decide
  have hdescent : baseEnd_1845388 < baseStart_1845388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845406 : List Nat := [4, 3, 1, 1, 4, 1, 2, 1, 1, 1, 4]
def baseStart_1845406 : Nat := 118140960795 + 1845406 * 2 ^ 59
def prefixEnd_1845406 : Nat := 4983230072969 + 3 ^ 40 * 1845406 * 2
def baseEnd_1845406 : Nat := 947580280691112074238139

theorem tailTrace_1845406 : CollatzResearch.WordTrace tailWord_1845406 prefixEnd_1845406 947580280691112074238139 := by
  unfold tailWord_1845406
  simp only [CollatzResearch.WordTrace]
  refine ⟨8413435794052088387240509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44871657568277804731949381 8413435794052088387240509)
  ·
    refine ⟨3155038422769533145215191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8413435794052088387240509 3155038422769533145215191)
    ·
      refine ⟨4732557634154299717822787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3155038422769533145215191 4732557634154299717822787)
      ·
        refine ⟨7098836451231449576734181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4732557634154299717822787 7098836451231449576734181)
        ·
          refine ⟨1331031834605896795637659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7098836451231449576734181 1331031834605896795637659)
          ·
            refine ⟨1996547751908845193456489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1331031834605896795637659 1996547751908845193456489)
            ·
              refine ⟨1497410813931633895092367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1996547751908845193456489 1497410813931633895092367)
              ·
                refine ⟨2246116220897450842638551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1497410813931633895092367 2246116220897450842638551)
                ·
                  refine ⟨3369174331346176263957827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2246116220897450842638551 3369174331346176263957827)
                  ·
                    refine ⟨5053761497019264395936741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3369174331346176263957827 5053761497019264395936741)
                    ·
                      refine ⟨947580280691112074238139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5053761497019264395936741 947580280691112074238139)
                      ·
                        rfl

theorem cell23_1845406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_1845406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1845406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1845406 prefixEnd_1845406 := by exact prefixLift 1845406
  have htrace : WordTrace (prefixWord ++ tailWord_1845406) baseStart_1845406 baseEnd_1845406 := by
    simpa [prefixWord, tailWord_1845406, baseEnd_1845406] using wordTrace_append hprefix tailTrace_1845406
  have hstable : (prefixWord ++ tailWord_1845406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845406).length < 2 ^ (prefixWord ++ tailWord_1845406).sum := by decide
  have hdescent : baseEnd_1845406 < baseStart_1845406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845445 : List Nat := [1, 3, 1, 1, 1, 1, 7, 1, 1, 4, 2]
def baseStart_1845445 : Nat := 118140960795 + 1845445 * 2 ^ 59
def prefixEnd_1845445 : Nat := 4983230072969 + 3 ^ 40 * 1845445 * 2
def baseEnd_1845445 : Nat := 947600306436637421650459

theorem tailTrace_1845445 : CollatzResearch.WordTrace tailWord_1845445 prefixEnd_1845445 947600306436637421650459 := by
  unfold tailWord_1845445
  simp only [CollatzResearch.WordTrace]
  refine ⟨67308908799275416758593789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44872605866183611172395859 67308908799275416758593789)
  ·
    refine ⟨25240840799728281284472671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67308908799275416758593789 25240840799728281284472671)
    ·
      refine ⟨37861261199592421926709007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25240840799728281284472671 37861261199592421926709007)
      ·
        refine ⟨56791891799388632890063511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37861261199592421926709007 56791891799388632890063511)
        ·
          refine ⟨85187837699082949335095267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56791891799388632890063511 85187837699082949335095267)
          ·
            refine ⟨127781756548624424002642901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85187837699082949335095267 127781756548624424002642901)
            ·
              refine ⟨2994884919108384937561943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 127781756548624424002642901 2994884919108384937561943)
              ·
                refine ⟨4492327378662577406342915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2994884919108384937561943 4492327378662577406342915)
                ·
                  refine ⟨6738491067993866109514373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4492327378662577406342915 6738491067993866109514373)
                  ·
                    refine ⟨1263467075248849895533945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6738491067993866109514373 1263467075248849895533945)
                    ·
                      refine ⟨947600306436637421650459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1263467075248849895533945 947600306436637421650459)
                      ·
                        rfl

theorem cell23_1845445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 1, 1, 4, 2].length) (baseStart_1845445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1845445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1845445 prefixEnd_1845445 := by exact prefixLift 1845445
  have htrace : WordTrace (prefixWord ++ tailWord_1845445) baseStart_1845445 baseEnd_1845445 := by
    simpa [prefixWord, tailWord_1845445, baseEnd_1845445] using wordTrace_append hprefix tailTrace_1845445
  have hstable : (prefixWord ++ tailWord_1845445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845445).length < 2 ^ (prefixWord ++ tailWord_1845445).sum := by decide
  have hdescent : baseEnd_1845445 < baseStart_1845445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845451 : List Nat := [1, 1, 1, 1, 3, 2, 3, 4, 7]
def baseStart_1845451 : Nat := 118140960795 + 1845451 * 2 ^ 59
def prefixEnd_1845451 : Nat := 4983230072969 + 3 ^ 40 * 1845451 * 2
def baseEnd_1845451 : Nat := 105289265257840488686159

theorem tailTrace_1845451 : CollatzResearch.WordTrace tailWord_1845451 prefixEnd_1845451 105289265257840488686159 := by
  unfold tailWord_1845451
  simp only [CollatzResearch.WordTrace]
  refine ⟨67309127637253679783312207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44872751758169119855541471 67309127637253679783312207)
  ·
    refine ⟨100963691455880519674968311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67309127637253679783312207 100963691455880519674968311)
    ·
      refine ⟨151445537183820779512452467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100963691455880519674968311 151445537183820779512452467)
      ·
        refine ⟨227168305775731169268678701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151445537183820779512452467 227168305775731169268678701)
        ·
          refine ⟨85188114665899188475754513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227168305775731169268678701 85188114665899188475754513)
          ·
            refine ⟨63891085999424391356815885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85188114665899188475754513 63891085999424391356815885)
            ·
              refine ⟨23959157249784146758805957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63891085999424391356815885 23959157249784146758805957)
              ·
                refine ⟨4492341984334527517276117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23959157249784146758805957 4492341984334527517276117)
                ·
                  refine ⟨105289265257840488686159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4492341984334527517276117 105289265257840488686159)
                  ·
                    rfl

theorem cell23_1845451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4, 7].length) (baseStart_1845451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1845451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1845451 prefixEnd_1845451 := by exact prefixLift 1845451
  have htrace : WordTrace (prefixWord ++ tailWord_1845451) baseStart_1845451 baseEnd_1845451 := by
    simpa [prefixWord, tailWord_1845451, baseEnd_1845451] using wordTrace_append hprefix tailTrace_1845451
  have hstable : (prefixWord ++ tailWord_1845451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845451).length < 2 ^ (prefixWord ++ tailWord_1845451).sum := by decide
  have hdescent : baseEnd_1845451 < baseStart_1845451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845535 : List Nat := [1, 1, 2, 4, 3, 1, 2, 2, 2, 1, 4]
def baseStart_1845535 : Nat := 118140960795 + 1845535 * 2 ^ 59
def prefixEnd_1845535 : Nat := 4983230072969 + 3 ^ 40 * 1845535 * 2
def baseEnd_1845535 : Nat := 947646519695542069525045

theorem tailTrace_1845535 : CollatzResearch.WordTrace tailWord_1845535 prefixEnd_1845535 947646519695542069525045 := by
  unfold tailWord_1845535
  simp only [CollatzResearch.WordTrace]
  refine ⟨67312191368949362129370059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44874794245966241419580039 67312191368949362129370059)
  ·
    refine ⟨100968287053424043194055089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67312191368949362129370059 100968287053424043194055089)
    ·
      refine ⟨75726215290068032395541317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100968287053424043194055089 75726215290068032395541317)
      ·
        refine ⟨14198665366887756074163997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75726215290068032395541317 14198665366887756074163997)
        ·
          refine ⟨5324499512582908527811499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14198665366887756074163997 5324499512582908527811499)
          ·
            refine ⟨7986749268874362791717249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5324499512582908527811499 7986749268874362791717249)
            ·
              refine ⟨5990061951655772093787937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7986749268874362791717249 5990061951655772093787937)
              ·
                refine ⟨4492546463741829070340953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5990061951655772093787937 4492546463741829070340953)
                ·
                  refine ⟨3369409847806371802755715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4492546463741829070340953 3369409847806371802755715)
                  ·
                    refine ⟨5054114771709557704133573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3369409847806371802755715 5054114771709557704133573)
                    ·
                      refine ⟨947646519695542069525045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5054114771709557704133573 947646519695542069525045)
                      ·
                        rfl

theorem cell23_1845535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_1845535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1845535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1845535 prefixEnd_1845535 := by exact prefixLift 1845535
  have htrace : WordTrace (prefixWord ++ tailWord_1845535) baseStart_1845535 baseEnd_1845535 := by
    simpa [prefixWord, tailWord_1845535, baseEnd_1845535] using wordTrace_append hprefix tailTrace_1845535
  have hstable : (prefixWord ++ tailWord_1845535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845535).length < 2 ^ (prefixWord ++ tailWord_1845535).sum := by decide
  have hdescent : baseEnd_1845535 < baseStart_1845535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845568 : List Nat := [2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 3]
def baseStart_1845568 : Nat := 118140960795 + 1845568 * 2 ^ 59
def prefixEnd_1845568 : Nat := 4983230072969 + 3 ^ 40 * 1845568 * 2
def baseEnd_1845568 : Nat := 947663464557140440412393

theorem tailTrace_1845568 : CollatzResearch.WordTrace tailWord_1845568 prefixEnd_1845568 947663464557140440412393 := by
  unfold tailWord_1845568
  simp only [CollatzResearch.WordTrace]
  refine ⟨33656697488914904382660679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44875596651886539176880905 33656697488914904382660679)
  ·
    refine ⟨50485046233372356573991019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33656697488914904382660679 50485046233372356573991019)
    ·
      refine ⟨75727569350058534860986529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50485046233372356573991019 75727569350058534860986529)
      ·
        refine ⟨56795677012543901145739897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75727569350058534860986529 56795677012543901145739897)
        ·
          refine ⟨42596757759407925859304923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56795677012543901145739897 42596757759407925859304923)
          ·
            refine ⟨63895136639111888788957385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42596757759407925859304923 63895136639111888788957385)
            ·
              refine ⟨47921352479333916591718039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63895136639111888788957385 47921352479333916591718039)
              ·
                refine ⟨71882028719000874887577059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47921352479333916591718039 71882028719000874887577059)
                ·
                  refine ⟨107823043078501312331365589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71882028719000874887577059 107823043078501312331365589)
                  ·
                    refine ⟨2527102572152374507766381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 107823043078501312331365589 2527102572152374507766381)
                    ·
                      refine ⟨947663464557140440412393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2527102572152374507766381 947663464557140440412393)
                      ·
                        rfl

theorem cell23_1845568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 3].length) (baseStart_1845568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1845568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1845568 prefixEnd_1845568 := by exact prefixLift 1845568
  have htrace : WordTrace (prefixWord ++ tailWord_1845568) baseStart_1845568 baseEnd_1845568 := by
    simpa [prefixWord, tailWord_1845568, baseEnd_1845568] using wordTrace_append hprefix tailTrace_1845568
  have hstable : (prefixWord ++ tailWord_1845568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845568).length < 2 ^ (prefixWord ++ tailWord_1845568).sum := by decide
  have hdescent : baseEnd_1845568 < baseStart_1845568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845569 : List Nat := [1, 2, 5, 2, 2, 2, 1, 1, 2, 1, 4]
def baseStart_1845569 : Nat := 118140960795 + 1845569 * 2 ^ 59
def prefixEnd_1845569 : Nat := 4983230072969 + 3 ^ 40 * 1845569 * 2
def baseEnd_1845569 : Nat := 947663978037794936499889

theorem tailTrace_1845569 : CollatzResearch.WordTrace tailWord_1845569 prefixEnd_1845569 947663978037794936499889 := by
  unfold tailWord_1845569
  simp only [CollatzResearch.WordTrace]
  refine ⟨67313431450826185936107761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44875620967217457290738507 67313431450826185936107761)
  ·
    refine ⟨50485073588119639452080821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67313431450826185936107761 50485073588119639452080821)
    ·
      refine ⟨4732975648886216198632577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50485073588119639452080821 4732975648886216198632577)
      ·
        refine ⟨3549731736664662148974433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4732975648886216198632577 3549731736664662148974433)
        ·
          refine ⟨2662298802498496611730825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3549731736664662148974433 2662298802498496611730825)
          ·
            refine ⟨1996724101873872458798119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2662298802498496611730825 1996724101873872458798119)
            ·
              refine ⟨2995086152810808688197179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1996724101873872458798119 2995086152810808688197179)
              ·
                refine ⟨4492629229216213032295769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2995086152810808688197179 4492629229216213032295769)
                ·
                  refine ⟨3369471921912159774221827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4492629229216213032295769 3369471921912159774221827)
                  ·
                    refine ⟨5054207882868239661332741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3369471921912159774221827 5054207882868239661332741)
                    ·
                      refine ⟨947663978037794936499889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5054207882868239661332741 947663978037794936499889)
                      ·
                        rfl

theorem cell23_1845569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_1845569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1845569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1845569 prefixEnd_1845569 := by exact prefixLift 1845569
  have htrace : WordTrace (prefixWord ++ tailWord_1845569) baseStart_1845569 baseEnd_1845569 := by
    simpa [prefixWord, tailWord_1845569, baseEnd_1845569] using wordTrace_append hprefix tailTrace_1845569
  have hstable : (prefixWord ++ tailWord_1845569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845569).length < 2 ^ (prefixWord ++ tailWord_1845569).sum := by decide
  have hdescent : baseEnd_1845569 < baseStart_1845569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845625 : List Nat := [1, 2, 1, 3, 2, 1, 1, 1, 1, 8, 2]
def baseStart_1845625 : Nat := 118140960795 + 1845625 * 2 ^ 59
def prefixEnd_1845625 : Nat := 4983230072969 + 3 ^ 40 * 1845625 * 2
def baseEnd_1845625 : Nat := 947692732954446717399631

theorem tailTrace_1845625 : CollatzResearch.WordTrace tailWord_1845625 prefixEnd_1845625 947692732954446717399631 := by
  unfold tailWord_1845625
  simp only [CollatzResearch.WordTrace]
  refine ⟨67315473938623307500146329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44876982625748871666764219 67315473938623307500146329)
  ·
    refine ⟨50486605453967480625109747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67315473938623307500146329 50486605453967480625109747)
    ·
      refine ⟨75729908180951220937664621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50486605453967480625109747 75729908180951220937664621)
      ·
        refine ⟨28398715567856707851624233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75729908180951220937664621 28398715567856707851624233)
        ·
          refine ⟨21299036675892530888718175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28398715567856707851624233 21299036675892530888718175)
          ·
            refine ⟨31948555013838796333077263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21299036675892530888718175 31948555013838796333077263)
            ·
              refine ⟨47922832520758194499615895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31948555013838796333077263 47922832520758194499615895)
              ·
                refine ⟨71884248781137291749423843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47922832520758194499615895 71884248781137291749423843)
                ·
                  refine ⟨107826373171705937624135765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71884248781137291749423843 107826373171705937624135765)
                  ·
                    refine ⟨1263590310605928956532841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 107826373171705937624135765 1263590310605928956532841)
                    ·
                      refine ⟨947692732954446717399631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1263590310605928956532841 947692732954446717399631)
                      ·
                        rfl

theorem cell23_1845625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 8, 2].length) (baseStart_1845625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1845625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1845625 prefixEnd_1845625 := by exact prefixLift 1845625
  have htrace : WordTrace (prefixWord ++ tailWord_1845625) baseStart_1845625 baseEnd_1845625 := by
    simpa [prefixWord, tailWord_1845625, baseEnd_1845625] using wordTrace_append hprefix tailTrace_1845625
  have hstable : (prefixWord ++ tailWord_1845625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845625).length < 2 ^ (prefixWord ++ tailWord_1845625).sum := by decide
  have hdescent : baseEnd_1845625 < baseStart_1845625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845672 : List Nat := [2, 1, 6, 1, 1, 1, 2, 1, 1, 1, 6]
def baseStart_1845672 : Nat := 118140960795 + 1845672 * 2 ^ 59
def prefixEnd_1845672 : Nat := 4983230072969 + 3 ^ 40 * 1845672 * 2
def baseEnd_1845672 : Nat := 947716866545208033511915

theorem tailTrace_1845672 : CollatzResearch.WordTrace tailWord_1845672 prefixEnd_1845672 947716866545208033511915 := by
  unfold tailWord_1845672
  simp only [CollatzResearch.WordTrace]
  refine ⟨33658594084726517263553635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44878125446302023018071513 33658594084726517263553635)
  ·
    refine ⟨50487891127089775895330453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33658594084726517263553635 50487891127089775895330453)
    ·
      refine ⟨2366619896582333245093615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 50487891127089775895330453 2366619896582333245093615)
      ·
        refine ⟨3549929844873499867640423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2366619896582333245093615 3549929844873499867640423)
        ·
          refine ⟨5324894767310249801460635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3549929844873499867640423 5324894767310249801460635)
          ·
            refine ⟨7987342150965374702190953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5324894767310249801460635 7987342150965374702190953)
            ·
              refine ⟨5990506613224031026643215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7987342150965374702190953 5990506613224031026643215)
              ·
                refine ⟨8985759919836046539964823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5990506613224031026643215 8985759919836046539964823)
                ·
                  refine ⟨13478639879754069809947235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8985759919836046539964823 13478639879754069809947235)
                  ·
                    refine ⟨20217959819631104714920853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13478639879754069809947235 20217959819631104714920853)
                    ·
                      refine ⟨947716866545208033511915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20217959819631104714920853 947716866545208033511915)
                      ·
                        rfl

theorem cell23_1845672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_1845672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1845672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1845672 prefixEnd_1845672 := by exact prefixLift 1845672
  have htrace : WordTrace (prefixWord ++ tailWord_1845672) baseStart_1845672 baseEnd_1845672 := by
    simpa [prefixWord, tailWord_1845672, baseEnd_1845672] using wordTrace_append hprefix tailTrace_1845672
  have hstable : (prefixWord ++ tailWord_1845672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845672).length < 2 ^ (prefixWord ++ tailWord_1845672).sum := by decide
  have hdescent : baseEnd_1845672 < baseStart_1845672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845692 : List Nat := [2, 2, 2, 4, 1, 1, 1, 1, 3, 3, 3]
def baseStart_1845692 : Nat := 118140960795 + 1845692 * 2 ^ 59
def prefixEnd_1845692 : Nat := 4983230072969 + 3 ^ 40 * 1845692 * 2
def baseEnd_1845692 : Nat := 947727136158297955261823

theorem tailTrace_1845692 : CollatzResearch.WordTrace tailWord_1845692 prefixEnd_1845692 947727136158297955261823 := by
  unfold tailWord_1845692
  simp only [CollatzResearch.WordTrace]
  refine ⟨33658958814690288971417665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44878611752920385295223553 33658958814690288971417665)
  ·
    refine ⟨25244219111017716728563249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33658958814690288971417665 25244219111017716728563249)
    ·
      refine ⟨18933164333263287546422437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25244219111017716728563249 18933164333263287546422437)
      ·
        refine ⟨3549968312486866414954207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18933164333263287546422437 3549968312486866414954207)
        ·
          refine ⟨5324952468730299622431311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3549968312486866414954207 5324952468730299622431311)
          ·
            refine ⟨7987428703095449433646967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5324952468730299622431311 7987428703095449433646967)
            ·
              refine ⟨11981143054643174150470451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7987428703095449433646967 11981143054643174150470451)
              ·
                refine ⟨17971714581964761225705677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11981143054643174150470451 17971714581964761225705677)
                ·
                  refine ⟨6739392968236785459639629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17971714581964761225705677 6739392968236785459639629)
                  ·
                    refine ⟨2527272363088794547364861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6739392968236785459639629 2527272363088794547364861)
                    ·
                      refine ⟨947727136158297955261823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2527272363088794547364861 947727136158297955261823)
                      ·
                        rfl

theorem cell23_1845692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_1845692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1845692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1845692 prefixEnd_1845692 := by exact prefixLift 1845692
  have htrace : WordTrace (prefixWord ++ tailWord_1845692) baseStart_1845692 baseEnd_1845692 := by
    simpa [prefixWord, tailWord_1845692, baseEnd_1845692] using wordTrace_append hprefix tailTrace_1845692
  have hstable : (prefixWord ++ tailWord_1845692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845692).length < 2 ^ (prefixWord ++ tailWord_1845692).sum := by decide
  have hdescent : baseEnd_1845692 < baseStart_1845692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845745 : List Nat := [1, 2, 2, 2, 3, 1, 1, 2, 1, 4, 4]
def baseStart_1845745 : Nat := 118140960795 + 1845745 * 2 ^ 59
def prefixEnd_1845745 : Nat := 4983230072969 + 3 ^ 40 * 1845745 * 2
def baseEnd_1845745 : Nat := 947754350632986247899079

theorem tailTrace_1845745 : CollatzResearch.WordTrace tailWord_1845745 prefixEnd_1845745 947754350632986247899079 := by
  unfold tailWord_1845745
  simp only [CollatzResearch.WordTrace]
  refine ⟨67319850698188567994514689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44879900465459045329676459 67319850698188567994514689)
  ·
    refine ⟨50489888023641425995886017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67319850698188567994514689 50489888023641425995886017)
    ·
      refine ⟨37867416017731069496914513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50489888023641425995886017 37867416017731069496914513)
      ·
        refine ⟨28400562013298302122685885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37867416017731069496914513 28400562013298302122685885)
        ·
          refine ⟨10650210754986863296007207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28400562013298302122685885 10650210754986863296007207)
          ·
            refine ⟨15975316132480294944010811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10650210754986863296007207 15975316132480294944010811)
            ·
              refine ⟨23962974198720442416016217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15975316132480294944010811 23962974198720442416016217)
              ·
                refine ⟨17972230649040331812012163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23962974198720442416016217 17972230649040331812012163)
                ·
                  refine ⟨26958345973560497718018245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17972230649040331812012163 26958345973560497718018245)
                  ·
                    refine ⟨5054689870042593322128421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26958345973560497718018245 5054689870042593322128421)
                    ·
                      refine ⟨947754350632986247899079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5054689870042593322128421 947754350632986247899079)
                      ·
                        rfl

theorem cell23_1845745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_1845745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1845745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1845745 prefixEnd_1845745 := by exact prefixLift 1845745
  have htrace : WordTrace (prefixWord ++ tailWord_1845745) baseStart_1845745 baseEnd_1845745 := by
    simpa [prefixWord, tailWord_1845745, baseEnd_1845745] using wordTrace_append hprefix tailTrace_1845745
  have hstable : (prefixWord ++ tailWord_1845745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845745).length < 2 ^ (prefixWord ++ tailWord_1845745).sum := by decide
  have hdescent : baseEnd_1845745 < baseStart_1845745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845772 : List Nat := [2, 2, 1, 2, 4, 2, 2, 1, 7]
def baseStart_1845772 : Nat := 118140960795 + 1845772 * 2 ^ 59
def prefixEnd_1845772 : Nat := 4983230072969 + 3 ^ 40 * 1845772 * 2
def baseEnd_1845772 : Nat := 105307579401184182473495

theorem tailTrace_1845772 : CollatzResearch.WordTrace tailWord_1845772 prefixEnd_1845772 105307579401184182473495 := by
  unfold tailWord_1845772
  simp only [CollatzResearch.WordTrace]
  refine ⟨33660417734545375802873785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44880556979393834403831713 33660417734545375802873785)
  ·
    refine ⟨25245313300909031852155339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33660417734545375802873785 25245313300909031852155339)
    ·
      refine ⟨37867969951363547778233009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25245313300909031852155339 37867969951363547778233009)
      ·
        refine ⟨28400977463522660833674757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37867969951363547778233009 28400977463522660833674757)
        ·
          refine ⟨5325183274410498906314017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28400977463522660833674757 5325183274410498906314017)
          ·
            refine ⟨3993887455807874179735513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5325183274410498906314017 3993887455807874179735513)
            ·
              refine ⟨2995415591855905634801635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3993887455807874179735513 2995415591855905634801635)
              ·
                refine ⟨4493123387783858452202453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2995415591855905634801635 4493123387783858452202453)
                ·
                  refine ⟨105307579401184182473495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4493123387783858452202453 105307579401184182473495)
                  ·
                    rfl

theorem cell23_1845772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 1, 7].length) (baseStart_1845772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1845772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1845772 prefixEnd_1845772 := by exact prefixLift 1845772
  have htrace : WordTrace (prefixWord ++ tailWord_1845772) baseStart_1845772 baseEnd_1845772 := by
    simpa [prefixWord, tailWord_1845772, baseEnd_1845772] using wordTrace_append hprefix tailTrace_1845772
  have hstable : (prefixWord ++ tailWord_1845772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845772).length < 2 ^ (prefixWord ++ tailWord_1845772).sum := by decide
  have hdescent : baseEnd_1845772 < baseStart_1845772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845783 : List Nat := [1, 1, 3, 6, 1, 2, 1, 1, 1, 4, 2]
def baseStart_1845783 : Nat := 118140960795 + 1845783 * 2 ^ 59
def prefixEnd_1845783 : Nat := 4983230072969 + 3 ^ 40 * 1845783 * 2
def baseEnd_1845783 : Nat := 947773862897857099223905

theorem tailTrace_1845783 : CollatzResearch.WordTrace tailWord_1845783 prefixEnd_1845783 947773862897857099223905 := by
  unfold tailWord_1845783
  simp only [CollatzResearch.WordTrace]
  refine ⟨67321236672050900484398003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44880824448033933656265335 67321236672050900484398003)
  ·
    refine ⟨100981855008076350726597005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67321236672050900484398003 100981855008076350726597005)
    ·
      refine ⟨37868195628028631522473877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100981855008076350726597005 37868195628028631522473877)
      ·
        refine ⟨1775071670063842102615963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 37868195628028631522473877 1775071670063842102615963)
        ·
          refine ⟨2662607505095763153923945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1775071670063842102615963 2662607505095763153923945)
          ·
            refine ⟨1996955628821822365442959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2662607505095763153923945 1996955628821822365442959)
            ·
              refine ⟨2995433443232733548164439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1996955628821822365442959 2995433443232733548164439)
              ·
                refine ⟨4493150164849100322246659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2995433443232733548164439 4493150164849100322246659)
                ·
                  refine ⟨6739725247273650483369989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4493150164849100322246659 6739725247273650483369989)
                  ·
                    refine ⟨1263698483863809465631873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6739725247273650483369989 1263698483863809465631873)
                    ·
                      refine ⟨947773862897857099223905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1263698483863809465631873 947773862897857099223905)
                      ·
                        rfl

theorem cell23_1845783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_1845783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1845783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1845783 prefixEnd_1845783 := by exact prefixLift 1845783
  have htrace : WordTrace (prefixWord ++ tailWord_1845783) baseStart_1845783 baseEnd_1845783 := by
    simpa [prefixWord, tailWord_1845783, baseEnd_1845783] using wordTrace_append hprefix tailTrace_1845783
  have hstable : (prefixWord ++ tailWord_1845783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845783).length < 2 ^ (prefixWord ++ tailWord_1845783).sum := by decide
  have hdescent : baseEnd_1845783 < baseStart_1845783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845785 : List Nat := [1, 2, 1, 2, 1, 1, 2, 4, 4, 5]
def baseStart_1845785 : Nat := 118140960795 + 1845785 * 2 ^ 59
def prefixEnd_1845785 : Nat := 4983230072969 + 3 ^ 40 * 1845785 * 2
def baseEnd_1845785 : Nat := 315924963286388697132965

theorem tailTrace_1845785 : CollatzResearch.WordTrace tailWord_1845785 prefixEnd_1845785 315924963286388697132965 := by
  unfold tailWord_1845785
  simp only [CollatzResearch.WordTrace]
  refine ⟨67321309618043654825970809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44880873078695769883980539 67321309618043654825970809)
  ·
    refine ⟨50490982213532741119478107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67321309618043654825970809 50490982213532741119478107)
    ·
      refine ⟨75736473320299111679217161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50490982213532741119478107 75736473320299111679217161)
      ·
        refine ⟨56802354990224333759412871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75736473320299111679217161 56802354990224333759412871)
        ·
          refine ⟨85203532485336500639119307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56802354990224333759412871 85203532485336500639119307)
          ·
            refine ⟨127805298728004750958678961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85203532485336500639119307 127805298728004750958678961)
            ·
              refine ⟨95853974046003563219009221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127805298728004750958678961 95853974046003563219009221)
              ·
                refine ⟨17972620133625668103564229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95853974046003563219009221 17972620133625668103564229)
                ·
                  refine ⟨3369866275054812769418293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17972620133625668103564229 3369866275054812769418293)
                  ·
                    refine ⟨315924963286388697132965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3369866275054812769418293 315924963286388697132965)
                    ·
                      rfl

theorem cell23_1845785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 4, 5].length) (baseStart_1845785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1845785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1845785 prefixEnd_1845785 := by exact prefixLift 1845785
  have htrace : WordTrace (prefixWord ++ tailWord_1845785) baseStart_1845785 baseEnd_1845785 := by
    simpa [prefixWord, tailWord_1845785, baseEnd_1845785] using wordTrace_append hprefix tailTrace_1845785
  have hstable : (prefixWord ++ tailWord_1845785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845785).length < 2 ^ (prefixWord ++ tailWord_1845785).sum := by decide
  have hdescent : baseEnd_1845785 < baseStart_1845785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845802 : List Nat := [3, 1, 4, 1, 1, 2, 2, 1, 1, 7]
def baseStart_1845802 : Nat := 118140960795 + 1845802 * 2 ^ 59
def prefixEnd_1845802 : Nat := 4983230072969 + 3 ^ 40 * 1845802 * 2
def baseEnd_1845802 : Nat := 315927873010097508295439

theorem tailTrace_1845802 : CollatzResearch.WordTrace tailWord_1845802 prefixEnd_1845802 315927873010097508295439 := by
  unfold tailWord_1845802
  simp only [CollatzResearch.WordTrace]
  refine ⟨16830482414745516682334915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44881286439321377819559773 16830482414745516682334915)
  ·
    refine ⟨25245723622118275023502373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16830482414745516682334915 25245723622118275023502373)
    ·
      refine ⟨4733573179147176566906695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25245723622118275023502373 4733573179147176566906695)
      ·
        refine ⟨7100359768720764850360043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4733573179147176566906695 7100359768720764850360043)
        ·
          refine ⟨10650539653081147275540065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7100359768720764850360043 10650539653081147275540065)
          ·
            refine ⟨7987904739810860456655049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10650539653081147275540065 7987904739810860456655049)
            ·
              refine ⟨5990928554858145342491287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7987904739810860456655049 5990928554858145342491287)
              ·
                refine ⟨8986392832287218013736931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5990928554858145342491287 8986392832287218013736931)
                ·
                  refine ⟨13479589248430827020605397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8986392832287218013736931 13479589248430827020605397)
                  ·
                    refine ⟨315927873010097508295439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13479589248430827020605397 315927873010097508295439)
                    ·
                      rfl

theorem cell23_1845802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_1845802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1845802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1845802 prefixEnd_1845802 := by exact prefixLift 1845802
  have htrace : WordTrace (prefixWord ++ tailWord_1845802) baseStart_1845802 baseEnd_1845802 := by
    simpa [prefixWord, tailWord_1845802, baseEnd_1845802] using wordTrace_append hprefix tailTrace_1845802
  have hstable : (prefixWord ++ tailWord_1845802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845802).length < 2 ^ (prefixWord ++ tailWord_1845802).sum := by decide
  have hdescent : baseEnd_1845802 < baseStart_1845802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845835 : List Nat := [1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 6]
def baseStart_1845835 : Nat := 118140960795 + 1845835 * 2 ^ 59
def prefixEnd_1845835 : Nat := 4983230072969 + 3 ^ 40 * 1845835 * 2
def baseEnd_1845835 : Nat := 947800563891890895773665

theorem tailTrace_1845835 : CollatzResearch.WordTrace tailWord_1845835 prefixEnd_1845835 947800563891890895773665 := by
  unfold tailWord_1845835
  simp only [CollatzResearch.WordTrace]
  refine ⟨67323133267862513365290959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44882088845241675576860639 67323133267862513365290959)
  ·
    refine ⟨100984699901793770047936439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67323133267862513365290959 100984699901793770047936439)
    ·
      refine ⟨151477049852690655071904659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100984699901793770047936439 151477049852690655071904659)
      ·
        refine ⟨227215574779035982607856989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151477049852690655071904659 227215574779035982607856989)
        ·
          refine ⟨85205840542138493477946371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227215574779035982607856989 85205840542138493477946371)
          ·
            refine ⟨127808760813207740216919557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85205840542138493477946371 127808760813207740216919557)
            ·
              refine ⟨23964142652476451290672417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127808760813207740216919557 23964142652476451290672417)
              ·
                refine ⟨17973106989357338468004313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23964142652476451290672417 17973106989357338468004313)
                ·
                  refine ⟨13479830242018003851003235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17973106989357338468004313 13479830242018003851003235)
                  ·
                    refine ⟨20219745363027005776504853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13479830242018003851003235 20219745363027005776504853)
                    ·
                      refine ⟨947800563891890895773665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20219745363027005776504853 947800563891890895773665)
                      ·
                        rfl

theorem cell23_1845835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 6].length) (baseStart_1845835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1845835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1845835 prefixEnd_1845835 := by exact prefixLift 1845835
  have htrace : WordTrace (prefixWord ++ tailWord_1845835) baseStart_1845835 baseEnd_1845835 := by
    simpa [prefixWord, tailWord_1845835, baseEnd_1845835] using wordTrace_append hprefix tailTrace_1845835
  have hstable : (prefixWord ++ tailWord_1845835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845835).length < 2 ^ (prefixWord ++ tailWord_1845835).sum := by decide
  have hdescent : baseEnd_1845835 < baseStart_1845835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845859 : List Nat := [1, 1, 1, 5, 1, 2, 4, 1, 2, 2, 3]
def baseStart_1845859 : Nat := 118140960795 + 1845859 * 2 ^ 59
def prefixEnd_1845859 : Nat := 4983230072969 + 3 ^ 40 * 1845859 * 2
def baseEnd_1845859 : Nat := 947812887427598801873555

theorem tailTrace_1845859 : CollatzResearch.WordTrace tailWord_1845859 prefixEnd_1845859 947812887427598801873555 := by
  unfold tailWord_1845859
  simp only [CollatzResearch.WordTrace]
  refine ⟨67324008619775565464164631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44882672413183710309443087 67324008619775565464164631)
  ·
    refine ⟨100986012929663348196246947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67324008619775565464164631 100986012929663348196246947)
    ·
      refine ⟨151479019394495022294370421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100986012929663348196246947 151479019394495022294370421)
      ·
        refine ⟨14201158068233908340097227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 151479019394495022294370421 14201158068233908340097227)
        ·
          refine ⟨21301737102350862510145841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14201158068233908340097227 21301737102350862510145841)
          ·
            refine ⟨15976302826763146882609381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21301737102350862510145841 15976302826763146882609381)
            ·
              refine ⟨2995556780018090040489259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15976302826763146882609381 2995556780018090040489259)
              ·
                refine ⟨4493335170027135060733889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2995556780018090040489259 4493335170027135060733889)
                ·
                  refine ⟨3370001377520351295550417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4493335170027135060733889 3370001377520351295550417)
                  ·
                    refine ⟨2527501033140263471662813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3370001377520351295550417 2527501033140263471662813)
                    ·
                      refine ⟨947812887427598801873555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2527501033140263471662813 947812887427598801873555)
                      ·
                        rfl

theorem cell23_1845859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_1845859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1845859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1845859 prefixEnd_1845859 := by exact prefixLift 1845859
  have htrace : WordTrace (prefixWord ++ tailWord_1845859) baseStart_1845859 baseEnd_1845859 := by
    simpa [prefixWord, tailWord_1845859, baseEnd_1845859] using wordTrace_append hprefix tailTrace_1845859
  have hstable : (prefixWord ++ tailWord_1845859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845859).length < 2 ^ (prefixWord ++ tailWord_1845859).sum := by decide
  have hdescent : baseEnd_1845859 < baseStart_1845859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845865 : List Nat := [1, 2, 1, 1, 1, 4, 1, 2, 1, 1, 8]
def baseStart_1845865 : Nat := 118140960795 + 1845865 * 2 ^ 59
def prefixEnd_1845865 : Nat := 4983230072969 + 3 ^ 40 * 1845865 * 2
def baseEnd_1845865 : Nat := 947815968311525778398527

theorem tailTrace_1845865 : CollatzResearch.WordTrace tailWord_1845865 prefixEnd_1845865 947815968311525778398527 := by
  unfold tailWord_1845865
  simp only [CollatzResearch.WordTrace]
  refine ⟨67324227457753828488883049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44882818305169218992588699 67324227457753828488883049)
  ·
    refine ⟨50493170593315371366662287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67324227457753828488883049 50493170593315371366662287)
    ·
      refine ⟨75739755889973057049993431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50493170593315371366662287 75739755889973057049993431)
      ·
        refine ⟨113609633834959585574990147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75739755889973057049993431 113609633834959585574990147)
        ·
          refine ⟨170414450752439378362485221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113609633834959585574990147 170414450752439378362485221)
          ·
            refine ⟨31952709516082383442965979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 170414450752439378362485221 31952709516082383442965979)
            ·
              refine ⟨47929064274123575164448969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31952709516082383442965979 47929064274123575164448969)
              ·
                refine ⟨35946798205592681373336727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47929064274123575164448969 35946798205592681373336727)
                ·
                  refine ⟨53920197308389022060005091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35946798205592681373336727 53920197308389022060005091)
                  ·
                    refine ⟨80880295962583533090007637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53920197308389022060005091 80880295962583533090007637)
                    ·
                      refine ⟨947815968311525778398527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 80880295962583533090007637 947815968311525778398527)
                      ·
                        rfl

theorem cell23_1845865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 1, 8].length) (baseStart_1845865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1845865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1845865 prefixEnd_1845865 := by exact prefixLift 1845865
  have htrace : WordTrace (prefixWord ++ tailWord_1845865) baseStart_1845865 baseEnd_1845865 := by
    simpa [prefixWord, tailWord_1845865, baseEnd_1845865] using wordTrace_append hprefix tailTrace_1845865
  have hstable : (prefixWord ++ tailWord_1845865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845865).length < 2 ^ (prefixWord ++ tailWord_1845865).sum := by decide
  have hdescent : baseEnd_1845865 < baseStart_1845865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845866 : List Nat := [3, 1, 3, 2, 1, 1, 2, 5, 1, 4]
def baseStart_1845866 : Nat := 118140960795 + 1845866 * 2 ^ 59
def prefixEnd_1845866 : Nat := 4983230072969 + 3 ^ 40 * 1845866 * 2
def baseEnd_1845866 : Nat := 315938827264060091495341

theorem tailTrace_1845866 : CollatzResearch.WordTrace tailWord_1845866 prefixEnd_1845866 315938827264060091495341 := by
  unfold tailWord_1845866
  simp only [CollatzResearch.WordTrace]
  refine ⟨16831065982687551414917363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44882842620500137106446301 16831065982687551414917363)
  ·
    refine ⟨25246598974031327122376045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16831065982687551414917363 25246598974031327122376045)
    ·
      refine ⟨9467474615261747670891017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25246598974031327122376045 9467474615261747670891017)
      ·
        refine ⟨7100605961446310753168263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9467474615261747670891017 7100605961446310753168263)
        ·
          refine ⟨10650908942169466129752395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7100605961446310753168263 10650908942169466129752395)
          ·
            refine ⟨15976363413254199194628593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10650908942169466129752395 15976363413254199194628593)
            ·
              refine ⟨11982272559940649395971445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15976363413254199194628593 11982272559940649395971445)
              ·
                refine ⟨1123338052494435880872323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11982272559940649395971445 1123338052494435880872323)
                ·
                  refine ⟨1685007078741653821308485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1123338052494435880872323 1685007078741653821308485)
                  ·
                    refine ⟨315938827264060091495341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1685007078741653821308485 315938827264060091495341)
                    ·
                      rfl

theorem cell23_1845866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 5, 1, 4].length) (baseStart_1845866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1845866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1845866 prefixEnd_1845866 := by exact prefixLift 1845866
  have htrace : WordTrace (prefixWord ++ tailWord_1845866) baseStart_1845866 baseEnd_1845866 := by
    simpa [prefixWord, tailWord_1845866, baseEnd_1845866] using wordTrace_append hprefix tailTrace_1845866
  have hstable : (prefixWord ++ tailWord_1845866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845866).length < 2 ^ (prefixWord ++ tailWord_1845866).sum := by decide
  have hdescent : baseEnd_1845866 < baseStart_1845866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845902 : List Nat := [4, 1, 1, 3, 1, 1, 1, 1, 2, 1, 7]
def baseStart_1845902 : Nat := 118140960795 + 1845902 * 2 ^ 59
def prefixEnd_1845902 : Nat := 4983230072969 + 3 ^ 40 * 1845902 * 2
def baseEnd_1845902 : Nat := 947834967095742133635857

theorem tailTrace_1845902 : CollatzResearch.WordTrace tailWord_1845902 prefixEnd_1845902 947834967095742133635857 := by
  unfold tailWord_1845902
  simp only [CollatzResearch.WordTrace]
  refine ⟨8415697119827472975997495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44883717972413189205319973 8415697119827472975997495)
  ·
    refine ⟨12623545679741209463996243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8415697119827472975997495 12623545679741209463996243)
    ·
      refine ⟨18935318519611814195994365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12623545679741209463996243 18935318519611814195994365)
      ·
        refine ⟨7100744444854430323497887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18935318519611814195994365 7100744444854430323497887)
        ·
          refine ⟨10651116667281645485246831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7100744444854430323497887 10651116667281645485246831)
          ·
            refine ⟨15976675000922468227870247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10651116667281645485246831 15976675000922468227870247)
            ·
              refine ⟨23965012501383702341805371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15976675000922468227870247 23965012501383702341805371)
              ·
                refine ⟨35947518752075553512708057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23965012501383702341805371 35947518752075553512708057)
                ·
                  refine ⟨26960639064056665134531043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35947518752075553512708057 26960639064056665134531043)
                  ·
                    refine ⟨40440958596084997701796565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26960639064056665134531043 40440958596084997701796565)
                    ·
                      refine ⟨947834967095742133635857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 40440958596084997701796565 947834967095742133635857)
                      ·
                        rfl

theorem cell23_1845902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_1845902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1845902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1845902 prefixEnd_1845902 := by exact prefixLift 1845902
  have htrace : WordTrace (prefixWord ++ tailWord_1845902) baseStart_1845902 baseEnd_1845902 := by
    simpa [prefixWord, tailWord_1845902, baseEnd_1845902] using wordTrace_append hprefix tailTrace_1845902
  have hstable : (prefixWord ++ tailWord_1845902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845902).length < 2 ^ (prefixWord ++ tailWord_1845902).sum := by decide
  have hdescent : baseEnd_1845902 < baseStart_1845902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845906 : List Nat := [3, 2, 3, 1, 2, 1, 1, 1, 5, 1, 3]
def baseStart_1845906 : Nat := 118140960795 + 1845906 * 2 ^ 59
def prefixEnd_1845906 : Nat := 4983230072969 + 3 ^ 40 * 1845906 * 2
def baseEnd_1845906 : Nat := 947837021018360117985839

theorem tailTrace_1845906 : CollatzResearch.WordTrace tailWord_1845906 prefixEnd_1845906 947837021018360117985839 := by
  unfold tailWord_1845906
  simp only [CollatzResearch.WordTrace]
  refine ⟨16831430712651323122781393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44883815233736861660750381 16831430712651323122781393)
  ·
    refine ⟨12623573034488492342086045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16831430712651323122781393 12623573034488492342086045)
    ·
      refine ⟨4733839887933184628282267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12623573034488492342086045 4733839887933184628282267)
      ·
        refine ⟨7100759831899776942423401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4733839887933184628282267 7100759831899776942423401)
        ·
          refine ⟨5325569873924832706817551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7100759831899776942423401 5325569873924832706817551)
          ·
            refine ⟨7988354810887249060226327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5325569873924832706817551 7988354810887249060226327)
            ·
              refine ⟨11982532216330873590339491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7988354810887249060226327 11982532216330873590339491)
              ·
                refine ⟨17973798324496310385509237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11982532216330873590339491 17973798324496310385509237)
                ·
                  refine ⟨1685043592921529098641491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17973798324496310385509237 1685043592921529098641491)
                  ·
                    refine ⟨2527565389382293647962237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1685043592921529098641491 2527565389382293647962237)
                    ·
                      refine ⟨947837021018360117985839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2527565389382293647962237 947837021018360117985839)
                      ·
                        rfl

theorem cell23_1845906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_1845906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1845906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1845906 prefixEnd_1845906 := by exact prefixLift 1845906
  have htrace : WordTrace (prefixWord ++ tailWord_1845906) baseStart_1845906 baseEnd_1845906 := by
    simpa [prefixWord, tailWord_1845906, baseEnd_1845906] using wordTrace_append hprefix tailTrace_1845906
  have hstable : (prefixWord ++ tailWord_1845906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845906).length < 2 ^ (prefixWord ++ tailWord_1845906).sum := by decide
  have hdescent : baseEnd_1845906 < baseStart_1845906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845916 : List Nat := [2, 2, 3, 2, 2, 2, 1, 1, 1, 5, 2]
def baseStart_1845916 : Nat := 118140960795 + 1845916 * 2 ^ 59
def prefixEnd_1845916 : Nat := 4983230072969 + 3 ^ 40 * 1845916 * 2
def baseEnd_1845916 : Nat := 947842155824905078860793

theorem tailTrace_1845916 : CollatzResearch.WordTrace tailWord_1845916 prefixEnd_1845916 947842155824905078860793 := by
  unfold tailWord_1845916
  simp only [CollatzResearch.WordTrace]
  refine ⟨33663043790284532099494801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44884058387046042799326401 33663043790284532099494801)
  ·
    refine ⟨25247282842713399074621101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33663043790284532099494801 25247282842713399074621101)
    ·
      refine ⟨9467731066017524652982913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25247282842713399074621101 9467731066017524652982913)
      ·
        refine ⟨7100798299513143489737185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9467731066017524652982913 7100798299513143489737185)
        ·
          refine ⟨5325598724634857617302889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7100798299513143489737185 5325598724634857617302889)
          ·
            refine ⟨3994199043476143212977167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5325598724634857617302889 3994199043476143212977167)
            ·
              refine ⟨5991298565214214819465751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3994199043476143212977167 5991298565214214819465751)
              ·
                refine ⟨8986947847821322229198627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5991298565214214819465751 8986947847821322229198627)
                ·
                  refine ⟨13480421771731983343797941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8986947847821322229198627 13480421771731983343797941)
                  ·
                    refine ⟨1263789541099873438481057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13480421771731983343797941 1263789541099873438481057)
                    ·
                      refine ⟨947842155824905078860793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1263789541099873438481057 947842155824905078860793)
                      ·
                        rfl

theorem cell23_1845916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_1845916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1845916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1845916 prefixEnd_1845916 := by exact prefixLift 1845916
  have htrace : WordTrace (prefixWord ++ tailWord_1845916) baseStart_1845916 baseEnd_1845916 := by
    simpa [prefixWord, tailWord_1845916, baseEnd_1845916] using wordTrace_append hprefix tailTrace_1845916
  have hstable : (prefixWord ++ tailWord_1845916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845916).length < 2 ^ (prefixWord ++ tailWord_1845916).sum := by decide
  have hdescent : baseEnd_1845916 < baseStart_1845916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845930 : List Nat := [3, 1, 5, 2, 2, 1, 1, 2, 6]
def baseStart_1845930 : Nat := 118140960795 + 1845930 * 2 ^ 59
def prefixEnd_1845930 : Nat := 4983230072969 + 3 ^ 40 * 1845930 * 2
def baseEnd_1845930 : Nat := 105316593839340891565081

theorem tailTrace_1845930 : CollatzResearch.WordTrace tailWord_1845930 prefixEnd_1845930 105316593839340891565081 := by
  unfold tailWord_1845930
  simp only [CollatzResearch.WordTrace]
  refine ⟨16831649550629586147499811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44884398801678896393332829 16831649550629586147499811)
  ·
    refine ⟨25247474325944379221249717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16831649550629586147499811 25247474325944379221249717)
    ·
      refine ⟨2366950718057285551992161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25247474325944379221249717 2366950718057285551992161)
      ·
        refine ⟨1775213038542964163994121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2366950718057285551992161 1775213038542964163994121)
        ·
          refine ⟨1331409778907223122995591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1775213038542964163994121 1331409778907223122995591)
          ·
            refine ⟨1997114668360834684493387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1331409778907223122995591 1997114668360834684493387)
            ·
              refine ⟨2995672002541252026740081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1997114668360834684493387 2995672002541252026740081)
              ·
                refine ⟨2246754001905939020055061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2995672002541252026740081 2246754001905939020055061)
                ·
                  refine ⟨105316593839340891565081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2246754001905939020055061 105316593839340891565081)
                  ·
                    rfl

theorem cell23_1845930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 2, 6].length) (baseStart_1845930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1845930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1845930 prefixEnd_1845930 := by exact prefixLift 1845930
  have htrace : WordTrace (prefixWord ++ tailWord_1845930) baseStart_1845930 baseEnd_1845930 := by
    simpa [prefixWord, tailWord_1845930, baseEnd_1845930] using wordTrace_append hprefix tailTrace_1845930
  have hstable : (prefixWord ++ tailWord_1845930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845930).length < 2 ^ (prefixWord ++ tailWord_1845930).sum := by decide
  have hdescent : baseEnd_1845930 < baseStart_1845930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845939 : List Nat := [1, 1, 1, 2, 3, 5, 1, 1, 4, 4]
def baseStart_1845939 : Nat := 118140960795 + 1845939 * 2 ^ 59
def prefixEnd_1845939 : Nat := 4983230072969 + 3 ^ 40 * 1845939 * 2
def baseEnd_1845939 : Nat := 315951321959986162957729

theorem tailTrace_1845939 : CollatzResearch.WordTrace tailWord_1845939 prefixEnd_1845939 315951321959986162957729 := by
  unfold tailWord_1845939
  simp only [CollatzResearch.WordTrace]
  refine ⟨67326926459485739127076871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44884617639657159418051247 67326926459485739127076871)
  ·
    refine ⟨100990389689228608690615307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67326926459485739127076871 100990389689228608690615307)
    ·
      refine ⟨151485584533842913035922961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100990389689228608690615307 151485584533842913035922961)
      ·
        refine ⟨113614188400382184776942221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151485584533842913035922961 113614188400382184776942221)
        ·
          refine ⟨42605320650143319291353333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113614188400382184776942221 42605320650143319291353333)
          ·
            refine ⟨3994248810950936183564375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42605320650143319291353333 3994248810950936183564375)
            ·
              refine ⟨5991373216426404275346563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3994248810950936183564375 5991373216426404275346563)
              ·
                refine ⟨8987059824639606413019845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5991373216426404275346563 8987059824639606413019845)
                ·
                  refine ⟨1685073717119926202441221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8987059824639606413019845 1685073717119926202441221)
                  ·
                    refine ⟨315951321959986162957729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1685073717119926202441221 315951321959986162957729)
                    ·
                      rfl

theorem cell23_1845939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 4, 4].length) (baseStart_1845939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1845939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1845939 prefixEnd_1845939 := by exact prefixLift 1845939
  have htrace : WordTrace (prefixWord ++ tailWord_1845939) baseStart_1845939 baseEnd_1845939 := by
    simpa [prefixWord, tailWord_1845939, baseEnd_1845939] using wordTrace_append hprefix tailTrace_1845939
  have hstable : (prefixWord ++ tailWord_1845939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845939).length < 2 ^ (prefixWord ++ tailWord_1845939).sum := by decide
  have hdescent : baseEnd_1845939 < baseStart_1845939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845949 : List Nat := [1, 4, 1, 2, 1, 4, 1, 2, 1, 1, 5]
def baseStart_1845949 : Nat := 118140960795 + 1845949 * 2 ^ 59
def prefixEnd_1845949 : Nat := 4983230072969 + 3 ^ 40 * 1845949 * 2
def baseEnd_1845949 : Nat := 947859100686503449748141

theorem tailTrace_1845949 : CollatzResearch.WordTrace tailWord_1845949 prefixEnd_1845949 947859100686503449748141 := by
  unfold tailWord_1845949
  simp only [CollatzResearch.WordTrace]
  refine ⟨67327291189449510834940901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44884860792966340556627267 67327291189449510834940901)
  ·
    refine ⟨12623867098021783281551419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67327291189449510834940901 12623867098021783281551419)
    ·
      refine ⟨18935800647032674922327129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12623867098021783281551419 18935800647032674922327129)
      ·
        refine ⟨14201850485274506191745347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18935800647032674922327129 14201850485274506191745347)
        ·
          refine ⟨21302775727911759287618021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14201850485274506191745347 21302775727911759287618021)
          ·
            refine ⟨3994270448983454866428379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21302775727911759287618021 3994270448983454866428379)
            ·
              refine ⟨5991405673475182299642569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3994270448983454866428379 5991405673475182299642569)
              ·
                refine ⟨4493554255106386724731927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5991405673475182299642569 4493554255106386724731927)
                ·
                  refine ⟨6740331382659580087097891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4493554255106386724731927 6740331382659580087097891)
                  ·
                    refine ⟨10110497073989370130646837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6740331382659580087097891 10110497073989370130646837)
                    ·
                      refine ⟨947859100686503449748141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10110497073989370130646837 947859100686503449748141)
                      ·
                        rfl

theorem cell23_1845949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_1845949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1845949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1845949 prefixEnd_1845949 := by exact prefixLift 1845949
  have htrace : WordTrace (prefixWord ++ tailWord_1845949) baseStart_1845949 baseEnd_1845949 := by
    simpa [prefixWord, tailWord_1845949, baseEnd_1845949] using wordTrace_append hprefix tailTrace_1845949
  have hstable : (prefixWord ++ tailWord_1845949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845949).length < 2 ^ (prefixWord ++ tailWord_1845949).sum := by decide
  have hdescent : baseEnd_1845949 < baseStart_1845949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845956 : List Nat := [2, 3, 3, 1, 1, 4, 1, 1, 1, 6]
def baseStart_1845956 : Nat := 118140960795 + 1845956 * 2 ^ 59
def prefixEnd_1845956 : Nat := 4983230072969 + 3 ^ 40 * 1845956 * 2
def baseEnd_1845956 : Nat := 315954231683694974120203

theorem tailTrace_1845956 : CollatzResearch.WordTrace tailWord_1845956 prefixEnd_1845956 315954231683694974120203 := by
  unfold tailWord_1845956
  simp only [CollatzResearch.WordTrace]
  refine ⟨33663773250212075515222861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44885031000282767353630481 33663773250212075515222861)
  ·
    refine ⟨12623914968829528318208573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33663773250212075515222861 12623914968829528318208573)
    ·
      refine ⟨4733968113311073119328215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12623914968829528318208573 4733968113311073119328215)
      ·
        refine ⟨7100952169966609678992323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4733968113311073119328215 7100952169966609678992323)
        ·
          refine ⟨10651428254949914518488485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7100952169966609678992323 10651428254949914518488485)
          ·
            refine ⟨1997142797803108972216591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10651428254949914518488485 1997142797803108972216591)
            ·
              refine ⟨2995714196704663458324887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1997142797803108972216591 2995714196704663458324887)
              ·
                refine ⟨4493571295056995187487331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2995714196704663458324887 4493571295056995187487331)
                ·
                  refine ⟨6740356942585492781230997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4493571295056995187487331 6740356942585492781230997)
                  ·
                    refine ⟨315954231683694974120203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6740356942585492781230997 315954231683694974120203)
                    ·
                      rfl

theorem cell23_1845956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_1845956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1845956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1845956 prefixEnd_1845956 := by exact prefixLift 1845956
  have htrace : WordTrace (prefixWord ++ tailWord_1845956) baseStart_1845956 baseEnd_1845956 := by
    simpa [prefixWord, tailWord_1845956, baseEnd_1845956] using wordTrace_append hprefix tailTrace_1845956
  have hstable : (prefixWord ++ tailWord_1845956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845956).length < 2 ^ (prefixWord ++ tailWord_1845956).sum := by decide
  have hdescent : baseEnd_1845956 < baseStart_1845956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845966 : List Nat := [4, 1, 1, 1, 3, 2, 1, 4, 1, 2, 3]
def baseStart_1845966 : Nat := 118140960795 + 1845966 * 2 ^ 59
def prefixEnd_1845966 : Nat := 4983230072969 + 3 ^ 40 * 1845966 * 2
def baseEnd_1845966 : Nat := 947867829857629883235563

theorem tailTrace_1845966 : CollatzResearch.WordTrace tailWord_1845966 prefixEnd_1845966 947867829857629883235563 := by
  unfold tailWord_1845966
  simp only [CollatzResearch.WordTrace]
  refine ⟨8415988903798490342288719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44885274153591948492206501 8415988903798490342288719)
  ·
    refine ⟨12623983355697735513433079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8415988903798490342288719 12623983355697735513433079)
    ·
      refine ⟨18935975033546603270149619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12623983355697735513433079 18935975033546603270149619)
      ·
        refine ⟨28403962550319904905224429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18935975033546603270149619 28403962550319904905224429)
        ·
          refine ⟨10651485956369964339459161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28403962550319904905224429 10651485956369964339459161)
          ·
            refine ⟨7988614467277473254594371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10651485956369964339459161 7988614467277473254594371)
            ·
              refine ⟨11982921700916209881891557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7988614467277473254594371 11982921700916209881891557)
              ·
                refine ⟨2246797818921789352854667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11982921700916209881891557 2246797818921789352854667)
                ·
                  refine ⟨3370196728382684029282001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2246797818921789352854667 3370196728382684029282001)
                  ·
                    refine ⟨2527647546287013021961501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3370196728382684029282001 2527647546287013021961501)
                    ·
                      refine ⟨947867829857629883235563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2527647546287013021961501 947867829857629883235563)
                      ·
                        rfl

theorem cell23_1845966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 4, 1, 2, 3].length) (baseStart_1845966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1845966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1845966 prefixEnd_1845966 := by exact prefixLift 1845966
  have htrace : WordTrace (prefixWord ++ tailWord_1845966) baseStart_1845966 baseEnd_1845966 := by
    simpa [prefixWord, tailWord_1845966, baseEnd_1845966] using wordTrace_append hprefix tailTrace_1845966
  have hstable : (prefixWord ++ tailWord_1845966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845966).length < 2 ^ (prefixWord ++ tailWord_1845966).sum := by decide
  have hdescent : baseEnd_1845966 < baseStart_1845966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845996 : List Nat := [2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 3]
def baseStart_1845996 : Nat := 118140960795 + 1845996 * 2 ^ 59
def prefixEnd_1845996 : Nat := 4983230072969 + 3 ^ 40 * 1845996 * 2
def baseEnd_1845996 : Nat := 947883234277264765860425

theorem tailTrace_1845996 : CollatzResearch.WordTrace tailWord_1845996 prefixEnd_1845996 947883234277264765860425 := by
  unfold tailWord_1845996
  simp only [CollatzResearch.WordTrace]
  refine ⟨33664502710139618930950921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44886003613519491907934561 33664502710139618930950921)
  ·
    refine ⟨25248377032604714198213191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33664502710139618930950921 25248377032604714198213191)
    ·
      refine ⟨37872565548907071297319787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25248377032604714198213191 37872565548907071297319787)
      ·
        refine ⟨56808848323360606945979681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37872565548907071297319787 56808848323360606945979681)
        ·
          refine ⟨42606636242520455209484761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56808848323360606945979681 42606636242520455209484761)
          ·
            refine ⟨31954977181890341407113571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42606636242520455209484761 31954977181890341407113571)
            ·
              refine ⟨47932465772835512110670357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31954977181890341407113571 47932465772835512110670357)
              ·
                refine ⟨2246834333101664630187673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47932465772835512110670357 2246834333101664630187673)
                ·
                  refine ⟨1685125749826248472640755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2246834333101664630187673 1685125749826248472640755)
                  ·
                    refine ⟨2527688624739372708961133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1685125749826248472640755 2527688624739372708961133)
                    ·
                      refine ⟨947883234277264765860425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2527688624739372708961133 947883234277264765860425)
                      ·
                        rfl

theorem cell23_1845996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 3].length) (baseStart_1845996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1845996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1845996 prefixEnd_1845996 := by exact prefixLift 1845996
  have htrace : WordTrace (prefixWord ++ tailWord_1845996) baseStart_1845996 baseEnd_1845996 := by
    simpa [prefixWord, tailWord_1845996, baseEnd_1845996] using wordTrace_append hprefix tailTrace_1845996
  have hstable : (prefixWord ++ tailWord_1845996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845996).length < 2 ^ (prefixWord ++ tailWord_1845996).sum := by decide
  have hdescent : baseEnd_1845996 < baseStart_1845996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845997 : List Nat := [1, 5, 1, 2, 1, 1, 5, 2, 1, 2, 2]
def baseStart_1845997 : Nat := 118140960795 + 1845997 * 2 ^ 59
def prefixEnd_1845997 : Nat := 4983230072969 + 3 ^ 40 * 1845997 * 2
def baseEnd_1845997 : Nat := 947883747757919261947921

theorem tailTrace_1845997 : CollatzResearch.WordTrace tailWord_1845997 prefixEnd_1845997 947883747757919261947921 := by
  unfold tailWord_1845997
  simp only [CollatzResearch.WordTrace]
  refine ⟨67329041893275615032688245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44886027928850410021792163 67329041893275615032688245)
  ·
    refine ⟨6312097677494588909314523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67329041893275615032688245 6312097677494588909314523)
    ·
      refine ⟨9468146516241883363971785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6312097677494588909314523 9468146516241883363971785)
      ·
        refine ⟨7101109887181412522978839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9468146516241883363971785 7101109887181412522978839)
        ·
          refine ⟨10651664830772118784468259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7101109887181412522978839 10651664830772118784468259)
          ·
            refine ⟨15977497246158178176702389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10651664830772118784468259 15977497246158178176702389)
            ·
              refine ⟨1497890366827329204065849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15977497246158178176702389 1497890366827329204065849)
              ·
                refine ⟨1123417775120496903049387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1497890366827329204065849 1123417775120496903049387)
                ·
                  refine ⟨1685126662680745354574081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1123417775120496903049387 1685126662680745354574081)
                  ·
                    refine ⟨1263844997010559015930561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1685126662680745354574081 1263844997010559015930561)
                    ·
                      refine ⟨947883747757919261947921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1263844997010559015930561 947883747757919261947921)
                      ·
                        rfl

theorem cell23_1845997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_1845997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1845997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1845997 prefixEnd_1845997 := by exact prefixLift 1845997
  have htrace : WordTrace (prefixWord ++ tailWord_1845997) baseStart_1845997 baseEnd_1845997 := by
    simpa [prefixWord, tailWord_1845997, baseEnd_1845997] using wordTrace_append hprefix tailTrace_1845997
  have hstable : (prefixWord ++ tailWord_1845997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845997).length < 2 ^ (prefixWord ++ tailWord_1845997).sum := by decide
  have hdescent : baseEnd_1845997 < baseStart_1845997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846023 : List Nat := [1, 1, 4, 4, 1, 2, 1, 1, 3, 3, 2]
def baseStart_1846023 : Nat := 118140960795 + 1846023 * 2 ^ 59
def prefixEnd_1846023 : Nat := 4983230072969 + 3 ^ 40 * 1846023 * 2
def baseEnd_1846023 : Nat := 947897098254936160222801

theorem tailTrace_1846023 : CollatzResearch.WordTrace tailWord_1846023 prefixEnd_1846023 947897098254936160222801 := by
  unfold tailWord_1846023
  simp only [CollatzResearch.WordTrace]
  refine ⟨67329990191181421473134723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44886660127454280982089815 67329990191181421473134723)
  ·
    refine ⟨100994985286772132209702085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67329990191181421473134723 100994985286772132209702085)
    ·
      refine ⟨18936559741269774789319141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100994985286772132209702085 18936559741269774789319141)
      ·
        refine ⟨3550604951488082772997339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18936559741269774789319141 3550604951488082772997339)
        ·
          refine ⟨5325907427232124159496009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3550604951488082772997339 5325907427232124159496009)
          ·
            refine ⟨3994430570424093119622007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5325907427232124159496009 3994430570424093119622007)
            ·
              refine ⟨5991645855636139679433011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3994430570424093119622007 5991645855636139679433011)
              ·
                refine ⟨8987468783454209519149517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5991645855636139679433011 8987468783454209519149517)
                ·
                  refine ⟨3370300793795328569681069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8987468783454209519149517 3370300793795328569681069)
                  ·
                    refine ⟨1263862797673248213630401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3370300793795328569681069 1263862797673248213630401)
                    ·
                      refine ⟨947897098254936160222801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1263862797673248213630401 947897098254936160222801)
                      ·
                        rfl

theorem cell23_1846023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_1846023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1846023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1846023 prefixEnd_1846023 := by exact prefixLift 1846023
  have htrace : WordTrace (prefixWord ++ tailWord_1846023) baseStart_1846023 baseEnd_1846023 := by
    simpa [prefixWord, tailWord_1846023, baseEnd_1846023] using wordTrace_append hprefix tailTrace_1846023
  have hstable : (prefixWord ++ tailWord_1846023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846023).length < 2 ^ (prefixWord ++ tailWord_1846023).sum := by decide
  have hdescent : baseEnd_1846023 < baseStart_1846023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846049 : List Nat := [1, 2, 3, 2, 1, 2, 2, 2, 2, 2, 4]
def baseStart_1846049 : Nat := 118140960795 + 1846049 * 2 ^ 59
def prefixEnd_1846049 : Nat := 4983230072969 + 3 ^ 40 * 1846049 * 2
def baseEnd_1846049 : Nat := 947910448751953058497681

theorem tailTrace_1846049 : CollatzResearch.WordTrace tailWord_1846049 prefixEnd_1846049 947910448751953058497681 := by
  unfold tailWord_1846049
  simp only [CollatzResearch.WordTrace]
  refine ⟨67330938489087227913581201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44887292326058151942387467 67330938489087227913581201)
  ·
    refine ⟨50498203866815420935185901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67330938489087227913581201 50498203866815420935185901)
    ·
      refine ⟨18936826450055782850694713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50498203866815420935185901 18936826450055782850694713)
      ·
        refine ⟨14202619837541837138021035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18936826450055782850694713 14202619837541837138021035)
        ·
          refine ⟨21303929756312755707031553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14202619837541837138021035 21303929756312755707031553)
          ·
            refine ⟨15977947317234566780273665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21303929756312755707031553 15977947317234566780273665)
            ·
              refine ⟨11983460487925925085205249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15977947317234566780273665 11983460487925925085205249)
              ·
                refine ⟨8987595365944443813903937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11983460487925925085205249 8987595365944443813903937)
                ·
                  refine ⟨6740696524458332860427953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8987595365944443813903937 6740696524458332860427953)
                  ·
                    refine ⟨5055522393343749645320965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6740696524458332860427953 5055522393343749645320965)
                    ·
                      refine ⟨947910448751953058497681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5055522393343749645320965 947910448751953058497681)
                      ·
                        rfl

theorem cell23_1846049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_1846049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1846049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1846049 prefixEnd_1846049 := by exact prefixLift 1846049
  have htrace : WordTrace (prefixWord ++ tailWord_1846049) baseStart_1846049 baseEnd_1846049 := by
    simpa [prefixWord, tailWord_1846049, baseEnd_1846049] using wordTrace_append hprefix tailTrace_1846049
  have hstable : (prefixWord ++ tailWord_1846049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846049).length < 2 ^ (prefixWord ++ tailWord_1846049).sum := by decide
  have hdescent : baseEnd_1846049 < baseStart_1846049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
